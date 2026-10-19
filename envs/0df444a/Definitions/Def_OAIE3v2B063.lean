-- Prove2me | Definitions.Def_OAIE3v2B063
-- name    : OAIE3v2B063
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:16:24.823744+00:00
-- url     : https://prove2.me/theorems/2dee8ef2-5a78-40d3-9d27-ac21215870cc
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 64 of 311
-- statement:
--   Definitions bundle 64 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B001`, `OAIE3v2B002`, `OAIE3v2B003`, `OAIE3v2B004`, `OAIE3v2B008`, `OAIE3v2B010`, `OAIE3v2B011`, `OAIE3v2B015`, `OAIE3v2B020`, `OAIE3v2B024`, `OAIE3v2B027`, `OAIE3v2B028`, `OAIE3v2B029`, `OAIE3v2B030`, `OAIE3v2B031`, `OAIE3v2B032` of this split.
--
--   Modules: `Dynamics/AnisotropicTupleChoiceBudget.lean`, `Dynamics/CandidatePhysicalOrdinaryBudget.lean`, `Dynamics/NormalizedTupleLargerBudget.lean`, `Dynamics/PreparedFiniteScheduleGeometryBudget.lean`, `Dynamics/PreparedModularCanonicalDetectorResourceBudget.lean`, `Dynamics/SharedWidthNormalizedTupleSideBudget.lean`, `Estimates/AllocatedAmbientLogBounds.lean`, `Estimates/AllocatedCandidateCommonFastGeometry.lean`, `Estimates/AllocatedCoverLogBounds.lean`, `Estimates/AllocatedExternalCandidateTaggedPairUniformFactors.lean`, `Estimates/AllocatedProfileDimensions.lean`, `Estimates/AllocatedScalarLogBounds.lean`, `Estimates/AllocatedShortAxis.lean`, `Estimates/AllocatedSlicedCoarseSource.lean`, `Estimates/AllocatedTupleSideThreshold.lean`, `Estimates/AnisotropicTupleErrorChoice.lean`, `Estimates/InitializedEarlyCanonicalSliceScales.lean`, `Estimates/MarginalTailModeling.lean`, `Estimates/PreparedFiniteForwardTreeStorage.lean`, `Estimates/PreparedModularGeneralDetectorNativeBounds.lean`, `Estimates/PreparedUniformEarlyRadiusWithCutoff.lean`, `Estimates/PrincipalAxisInterpolation.lean`, `Estimates/ResidualErrorAllocation.lean`, `Estimates/SmoothSublevelCutoff.lean`, `Geometry/AllocatedProductChartRadius.lean`, `Geometry/AnisotropicSpatialCapBudget.lean`, `Geometry/SmoothSpatialCostBudget.lean`, `Geometry/SpatialNumericEnvelopeFunctoriality.lean`, `Geometry/UnconditionedSpatialWidthBudget.lean`, `Lattices/AllocatedAffineCanonicalBackendBudget.lean`, `Lattices/AllocatedAffinePhysicalTerminalReset.lean`, `Lattices/AllocatedAffineScaleEnvelope.lean`, `Lattices/AllocatedLocalResidueReconstruction.lean`, `Lattices/IntegerRowInterpolationMixture.lean`, `Lattices/PartitionedAffineLogEnvelope.lean`, `Linear/AllocatedCanonicalProjectionBudget.lean`, `Linear/BalancedDualBounds.lean`, `Linear/KernelScalarEnvelope.lean`, `Linear/RationalTagProjectionComplement.lean`, `Polynomial/IntegerPolynomialInterpolation.lean`, `Polynomial/PolynomialShearParameterBudget.lean`, `Probability/DensityMixtureAELaw.lean`, `Sampling/RealMatrixSpecifiedGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B000
import Definitions.Def_OAIE3v2B001
import Definitions.Def_OAIE3v2B002
import Definitions.Def_OAIE3v2B003
import Definitions.Def_OAIE3v2B004
import Definitions.Def_OAIE3v2B008
import Definitions.Def_OAIE3v2B010
import Definitions.Def_OAIE3v2B011
import Definitions.Def_OAIE3v2B015
import Definitions.Def_OAIE3v2B020
import Definitions.Def_OAIE3v2B024
import Definitions.Def_OAIE3v2B027
import Definitions.Def_OAIE3v2B028
import Definitions.Def_OAIE3v2B029
import Definitions.Def_OAIE3v2B030
import Definitions.Def_OAIE3v2B031
import Definitions.Def_OAIE3v2B032

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BalancedDualBounds
namespace OAI

section

namespace Erdos3

theorem norm_lt_of_re_lt_on_balanced {E : Type*} [AddCommGroup E] [Module ℂ E]
    (f : E →ₗ[ℂ] ℂ) {S : Set E} (hS : Balanced ℂ S) {c : ℝ}
    (hf : ∀ x ∈ S, (f x).re < c) : ∀ x ∈ S, ‖f x‖ < c := by
  intro x hx
  obtain ⟨a, ha, hphase⟩ := exists_complex_unit_phase (f x)
  have h := hf (a • x) (hS.smul_mem ha.le hx)
  simpa only [map_smul, smul_eq_mul, hphase, Complex.ofReal_re] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothSublevelCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

theorem exists_smooth_sublevel_cutoff :
    ∃ A : ℝ≥0, 1 ≤ A ∧ ∃ ψ : ℝ → ℝ,
      ContDiff ℝ ∞ ψ ∧ (∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ t, |t| ≤ 1 → ψ t = 0) ∧
      (∀ t, 2 ≤ |t| → ψ t = 1) ∧ LipschitzWith A ψ := by
  obtain ⟨A, hA, χ, hs, hrange, hone, hzero, hLip⟩ := exists_smooth_scalar_cutoff
  refine ⟨A, hA, fun t => 1 - χ (t / 2), ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_const.sub (hs.comp (contDiff_id.div_const 2))
  · intro t
    exact ⟨sub_nonneg.mpr (hrange _).2, by linarith [(hrange (t / 2)).1]⟩
  · intro t ht
    have ht' : |t / 2| ≤ 1 / 2 := by rw [abs_div]; norm_num; linarith
    simp only [hone (t / 2) ht', sub_self]
  · intro t ht
    have ht' : 3 / 4 ≤ |t / 2| := by rw [abs_div]; norm_num; linarith
    simp only [hzero (t / 2) ht', sub_zero]
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := hLip.dist_le_mul (x / 2) (y / 2)
    rw [Real.dist_eq, Real.dist_eq, ← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    rw [Real.dist_eq, Real.dist_eq]
    have heq : (1 - χ (x / 2)) - (1 - χ (y / 2)) = -(χ (x / 2) - χ (y / 2)) := by ring
    rw [heq, abs_neg]
    exact h.trans (by nlinarith [A.coe_nonneg, abs_nonneg (x - y)])

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
namespace OAI

section

namespace Erdos3

theorem twoTermErrorChoices_log_bounds {T A B ε P : ℝ}
    (hA0 : 0 ≤ A) (_hB0 : 0 ≤ B) (hε : 0 < ε) (hP : 0 ≤ P)
    (hT : T ≤ Real.exp P) (hA : A ≤ Real.exp P) (hB : B ≤ Real.exp P)
    (hi : ε⁻¹ ≤ Real.exp P) :
    twoTermErrorResolution T A ε ≤ Real.exp (2*P+4) ∧
    (twoTermErrorWidth B ε)⁻¹ ≤ Real.exp (2*P+4) := by
  have h1 : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have hsq : Real.exp P ≤ (Real.exp P)^2 := by nlinarith
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hbound : 4*(Real.exp P)^2 ≤ Real.exp (2*P+4) := by
    calc
      _ ≤ Real.exp 4*(Real.exp P)^2 := mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  constructor
  · apply le_trans _ hbound
    unfold twoTermErrorResolution
    rw [div_eq_mul_inv]
    have hm : 2*A*ε⁻¹ ≤ 2*Real.exp P*Real.exp P := by gcongr
    nlinarith
  · unfold twoTermErrorWidth
    apply inv_min_le_of_inv_le
    · simpa only [inv_one] using Real.one_le_exp_iff.mpr (by positivity : 0 ≤ 2*P+4)
    · apply le_trans _ hbound
      rw [inv_div, div_eq_mul_inv]
      have hm : 2*(1+B)*ε⁻¹ ≤ 2*(1+Real.exp P)*Real.exp P := by gcongr
      nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityMixtureAELaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem pmf_realDensity_count {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : PMF X) : p.toMeasure = realDensityMeasure Measure.count (fun x => (p x).toReal) := by
  ext s hs
  rw [p.toMeasure_apply hs, realDensityMeasure, withDensity_apply _ hs]
  simp_rw [ENNReal.ofReal_toReal (p.apply_ne_top _)]
  rw [← lintegral_indicator (μ := Measure.count) hs p, lintegral_count]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Function _root_.Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem realDensityMeasure_map_embedding (e : X → Y) (he : MeasurableEmbedding e)
    (μ : Measure X) (f : X → ℝ) :
    Measure.map e (realDensityMeasure μ f) =
      realDensityMeasure (Measure.map e μ) (Function.extend e f (fun _ => 0)) := by
  ext S hS
  rw [Measure.map_apply he.measurable hS, realDensityMeasure, realDensityMeasure,
    withDensity_apply _ (hS.preimage he.measurable), withDensity_apply _ hS,
    he.restrict_map, he.lintegral_map]
  simp only [he.injective.extend_apply]

theorem realDensityMeasure_restrict_support (ν : Measure Y) (f : Y → ℝ)
    {S : Set Y} (hS : MeasurableSet S) (hf : ∀ y ∉ S, f y = 0) :
    realDensityMeasure (ν.restrict S) f = realDensityMeasure ν f := by
  unfold realDensityMeasure
  rw [← withDensity_indicator hS]
  congr 1
  ext y
  by_cases hy : y ∈ S
  · simp only [Set.indicator_of_mem hy]
  · simp only [Set.indicator_of_notMem hy, hf y hy, ENNReal.ofReal_zero]

theorem realDensityMeasure_smul_real (ν : Measure Y) (f : Y → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    realDensityMeasure (ENNReal.ofReal c • ν) f = realDensityMeasure ν (fun y => c * f y) := by
  unfold realDensityMeasure
  rw [withDensity_smul_measure]
  have he : (fun y => ENNReal.ofReal (c * f y)) =
      ENNReal.ofReal c • (fun y => ENNReal.ofReal (f y)) := by
    funext y
    exact ENNReal.ofReal_mul hc
  rw [he, withDensity_smul' _ _ ENNReal.ofReal_ne_top]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem shearDisplacementBound_le_exp (s d : ℕ) (M : ℝ≥0) :
    (polynomialShearDisplacementBound s d ((1 + M) ^ (s * d)) : ℝ) ≤
      Real.exp (shearActionLogBudget s d M) := by
  have hs : (s : ℝ) ≤ Real.exp (s : ℝ) := by linarith [Real.add_one_le_exp (s : ℝ)]
  let J : ℝ := d * ((s + 1) * (d + 1) ^ s) * s
  have hB : 1 + J ≤ Real.exp J := by linarith [Real.add_one_le_exp J]
  have hR := shearRadius_le_exp s d M
  have he : (polynomialShearDisplacementBound s d ((1 + M) ^ (s * d)) : ℝ) =
      (s : ℝ) * (1 + J) ^ s * ((((1 + M) ^ (s * d) : ℝ≥0) : ℝ) ^ s) := by
    simp [polynomialShearDisplacementBound, J]
  rw [he]
  calc
    _ ≤ Real.exp (s : ℝ) * (Real.exp J) ^ s *
        (Real.exp ((s * d : ℕ) * (M : ℝ))) ^ s := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [J, shearActionLogBudget]
      push_cast
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture
namespace OAI

section

namespace Erdos3

noncomputable def constantIntegerInterpolationCap (δ : ℝ) : ℝ :=
  8 * (probabilityProfileLipschitz : ℝ) / δ

noncomputable def constantIntegerInterpolationLip (δ : ℝ) : ℝ :=
  max (2 * (probabilityProfileLipschitz : ℝ) / δ ^ 2)
    (2 * (constantIntegerInterpolationCap δ) ^ 2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedShortAxis
namespace OAI

section

namespace Erdos3

noncomputable def tailAxisInterpolationLip (L s : ℕ) (ε : ℝ) : ℝ :=
  max (2 * (probabilityProfileLipschitz : ℝ) * ((L : ℝ)^s)^2 / ε^2)
    (2 * ((L : ℝ)^(s+1))^2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalAxisInterpolation
namespace OAI

section

namespace Erdos3

noncomputable def principalAxisInterpolationLip (h L : ℕ) (γ : ℝ) : ℝ :=
  max (8 * (probabilityProfileLipschitz : ℝ) * ((L : ℝ)^h)^2 / γ^2)
    (2 * ((L : ℝ)^h)^2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialInterpolation
namespace OAI

section

namespace Erdos3

variable {J V : Type*} [Fintype J]

noncomputable def integerPolynomialInterpolationCap (h L s : ℕ) (ρ γ ε : ℝ) : ℝ :=
  max (constantIntegerInterpolationCap ρ)
    (max (principalAxisInterpolationCap h L γ) (tailAxisInterpolationCap L s ε))

noncomputable def integerPolynomialInterpolationLip (h L s : ℕ) (ρ γ ε : ℝ) : ℝ :=
  max (constantIntegerInterpolationLip ρ)
    (max (principalAxisInterpolationLip h L γ) (tailAxisInterpolationLip L s ε))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedScalarLogBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedLayerIntegerInterpolationCap (R σ : Fin m → ℝ) (L : ℕ)
    (j : Fin m) (i : Fin (n j)) : ℝ :=
  integerPolynomialInterpolationCap (j.val+1) L (layerTailDegree m) (R j / 4)
    (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)
    (tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))))

noncomputable def allocatedLayerIntegerInterpolationLip (R σ : Fin m → ℝ) (L : ℕ)
    (j : Fin m) (i : Fin (n j)) : ℝ :=
  integerPolynomialInterpolationLip (j.val+1) L (layerTailDegree m) (R j / 4)
    (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)
    (tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedLayerCommonCap (R σ : Fin m → ℝ) (L : ℕ) (j : Fin m) : ℝ≥0 :=
  1 + ∑ i, Real.toNNReal (allocatedLayerIntegerInterpolationCap (G := G) B R σ L j i)

noncomputable def allocatedLayerCommonLip (R σ : Fin m → ℝ) (L : ℕ) (j : Fin m) : ℝ≥0 :=
  ∑ i, Real.toNNReal (allocatedLayerIntegerInterpolationLip (G := G) B R σ L j i)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators NNReal

def allocatedScalarLog (m : ℕ) (P : ℝ) : ℝ :=
  7 * integerInterpolationLogEnvelope (layerTailDegree m) (4 * (P+8))

def allocatedCommonLog (m : ℕ) (P : ℝ) : ℝ := P + P * allocatedScalarLog m P + 1

theorem allocatedScalarLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ allocatedScalarLog m P := by
  unfold allocatedScalarLog integerInterpolationLogEnvelope
  positivity

theorem allocatedCommonLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ allocatedCommonLog m P := by
  have h := allocatedScalarLog_nonneg m hP
  unfold allocatedCommonLog
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedAmbientLogBounds
namespace OAI

section

namespace Erdos3

def allocatedMixedLog (m : ℕ) (P : ℝ) : ℝ :=
  (2*P+1)*(allocatedWidthLog m P + allocatedCommonLog m P)+3*P+1

theorem allocatedMixedLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ allocatedMixedLog m P := by
  have hw := allocatedWidthLog_nonneg m hP
  have hc := allocatedCommonLog_nonneg m hP
  unfold allocatedMixedLog
  positivity

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

def allocatedAmbientLog (m : ℕ) (P : ℝ) : ℝ :=
  P + P*(2*allocatedMixedLog m P+4*P+9)+1

theorem allocatedAmbientLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ allocatedAmbientLog m P := by
  have h := allocatedMixedLog_nonneg m hP
  unfold allocatedAmbientLog
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem le_spatialSamplingBudget {P : ℝ} (hP : 0 ≤ P) : P ≤ spatialSamplingBudget P := by
  unfold spatialSamplingBudget
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarginalTailModeling
namespace OAI

section

namespace Erdos3

open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem exists_modeling_dual_obstruction (X : Seminorm ℂ E) {S : Set E}
    (hS : Balanced ℂ S) (hSn : S.Nonempty) {R tau : ℝ} (hR : 0 < R) (htau : 0 < tau)
    (b : E) (hb : b ∉ closure (R • convexHull ℝ S + X.closedBall 0 tau)) :
    ∃ f : E →L[ℂ] ℂ, 1 < (f b).re ∧
      (∀ v, tau * ‖f v‖ ≤ X v) ∧ (∀ Q ∈ S, R * ‖f Q‖ < 1) := by
  let A : Set E := R • convexHull ℝ S + X.closedBall 0 tau
  have hconv : Convex ℝ A :=
    ((convex_convexHull ℝ S).smul R).add (X.convex_closedBall 0 tau)
  have hzS : (0 : E) ∈ convexHull ℝ S := subset_convexHull ℝ S (hS.zero_mem hSn)
  have hzR : (0 : E) ∈ R • convexHull ℝ S := by
    simpa only [smul_zero] using Set.smul_mem_smul_set (a := R) hzS
  have hzBall : (0 : E) ∈ X.closedBall 0 tau := X.mem_closedBall_self htau.le
  have hz : (0 : E) ∈ A := by
    simpa only [add_zero] using Set.add_mem_add hzR hzBall
  obtain ⟨g, u, hgu, hub⟩ := RCLike.geometric_hahn_banach_closed_point
    (𝕜 := ℂ) hconv.closure isClosed_closure hb
  have hu : 0 < u := by simpa only [map_zero, Complex.zero_re] using hgu 0 (subset_closure hz)
  let f : E →L[ℂ] ℂ := (u⁻¹ : ℝ) • g
  have hf (v : E) : (f v).re = (g v).re / u := by
    change (u⁻¹ • g v).re = _
    rw [Complex.smul_re, smul_eq_mul]
    ring
  have hfb : 1 < (f b).re := by
    rw [hf]
    exact (lt_div_iff₀ hu).mpr (by simpa using hub)
  have hfa : ∀ v ∈ A, (f v).re < 1 := by
    intro v hv
    rw [hf]
    exact (div_lt_iff₀ hu).mpr (by simpa using hgu v (subset_closure hv))
  have hballRe : ∀ v ∈ X.closedBall 0 tau, (f v).re < 1 := by
    intro v hv
    apply hfa
    simpa only [zero_add] using Set.add_mem_add hzR hv
  have hballNorm := norm_lt_of_re_lt_on_balanced f.toLinearMap
    (X.balanced_closedBall_zero tau) hballRe
  have hdual : ∀ v, tau * ‖f v‖ ≤ X v :=
    seminorm_dual_bound_of_ball X f.toLinearMap htau
      (fun v hv => hballNorm v (X.mem_closedBall_zero.mpr hv))
  have hstructRe : ∀ Q ∈ S, (((R : ℝ) • f) Q).re < 1 := by
    intro Q hQ
    have hRQ : R • Q ∈ R • convexHull ℝ S :=
      Set.smul_mem_smul_set (subset_convexHull ℝ S hQ)
    have hQA : R • Q ∈ A := by
      simpa only [add_zero] using Set.add_mem_add hRQ hzBall
    simpa only [smul_apply, ContinuousLinearMap.map_smul_of_tower] using hfa _ hQA
  have hstruct := norm_lt_of_re_lt_on_balanced ((R : ℝ) • f).toLinearMap hS hstructRe
  refine ⟨f, hfb, hdual, ?_⟩
  intro Q hQ
  have h := hstruct Q hQ
  change ‖R • f Q‖ < 1 at h
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hR] using h

theorem mem_closure_model_set_of_dual_detector (X : Seminorm ℂ E) {S : Set E}
    (hS : Balanced ℂ S) (hSn : S.Nonempty) {R tau : ℝ} (hR : 0 < R) (htau : 0 < tau)
    (b : E)
    (hdetect : ∀ f : E →L[ℂ] ℂ, 1 < (f b).re → (∀ v, tau * ‖f v‖ ≤ X v) →
      ∃ Q ∈ S, 1 ≤ R * ‖f Q‖) :
    b ∈ closure (R • convexHull ℝ S + X.closedBall 0 tau) := by
  by_contra hb
  obtain ⟨f, hfb, hdual, hsmall⟩ := exists_modeling_dual_obstruction X hS hSn hR htau b hb
  obtain ⟨Q, hQ, hlarge⟩ := hdetect f hfb hdual
  exact (hsmall Q hQ).not_ge hlarge

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SmoothSpatialCostBudget
namespace OAI

section

namespace Erdos3

theorem selectedColumn_card {I J : Type*} [Fintype I] [Fintype J] (s : I ↪ J) :
    Fintype.card I + Fintype.card (UnselectedColumn s) = Fintype.card J := by
  simpa only [Fintype.card_sum] using Fintype.card_congr (selectedColumnEquiv s)

theorem scalarSpatialInverseAllowance_le_exp (I : Type*) [Fintype I] {B : ℕ} {R : ℝ}
    (hB : (B : ℝ) ≤ Real.exp R) :
    scalarSpatialInverseAllowance I B ≤
      Real.exp ((Fintype.card I + 1 : ℝ) + (Fintype.card I + 1 : ℝ)^2 + R) := by
  have hn : (Fintype.card I + 1 : ℝ) ≤ Real.exp (Fintype.card I + 1 : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card I + 1 : ℝ)]
  have hf : ((Fintype.card I + 1).factorial : ℝ) ≤ Real.exp ((Fintype.card I + 1 : ℝ)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using factorial_le_exp_sq (Fintype.card I + 1)
  unfold scalarSpatialInverseAllowance
  calc
    _ ≤ Real.exp (Fintype.card I + 1 : ℝ) * Real.exp ((Fintype.card I + 1 : ℝ)^2) * Real.exp R := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def spatialProfileLog (j d : ℕ) (p : ℝ) : ℝ :=
  (j+1)*p+(j : ℝ)^2+2*j+d+probabilityProfileLipschitz+1

theorem spatialProfileLog_nonneg (j d : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ spatialProfileLog j d p := by unfold spatialProfileLog; positivity

theorem spatialProfileLog_bounds {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) {M : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hM : (M : ℝ) ≤ Real.exp p) :
    let j := Fintype.card (Unit ⊕ I)
    let d := Fintype.card (UnselectedColumn s ⊕ N)
    let P := spatialProfileLog j d p
    scalarSpatialIndexAllowance I M ≤ Real.exp P ∧
    scalarSpatialInverseAllowance I M ≤ Real.exp P ∧
    (d : ℝ) ≤ Real.exp P ∧
    ((d+j : ℝ)*probabilityProfileLipschitz) ≤ Real.exp P := by
  dsimp only
  let j := Fintype.card (Unit ⊕ I)
  let d := Fintype.card (UnselectedColumn s ⊕ N)
  have hj : (Fintype.card I+1 : ℝ) = j := by
    simp only [j, Fintype.card_sum, Fintype.card_unit, Nat.cast_add, Nat.cast_one]
    ring
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hκ : (0 : ℝ) ≤ probabilityProfileLipschitz := NNReal.coe_nonneg _
  have hG := scalarSpatialIndexAllowance_le_exp I hM
  have hU := scalarSpatialInverseAllowance_le_exp I hM
  rw [hj] at hG hU
  have hn : (d+j : ℝ) ≤ Real.exp (d+j : ℝ) := by
    linarith [Real.add_one_le_exp (d+j : ℝ)]
  have hk : (probabilityProfileLipschitz : ℝ) ≤ Real.exp probabilityProfileLipschitz := by
    linarith [Real.add_one_le_exp (probabilityProfileLipschitz : ℝ)]
  refine ⟨hG.trans (Real.exp_le_exp.mpr ?_), hU.trans (Real.exp_le_exp.mpr ?_), ?_, ?_⟩
  · change (j : ℝ)*p ≤ spatialProfileLog j d p
    unfold spatialProfileLog
    nlinarith
  · change (j : ℝ)+j^2+p ≤ spatialProfileLog j d p
    unfold spatialProfileLog
    nlinarith
  · calc
      (d : ℝ) ≤ Real.exp d := by linarith [Real.add_one_le_exp (d : ℝ)]
      _ ≤ Real.exp (spatialProfileLog j d p) := by
        apply Real.exp_le_exp.mpr
        unfold spatialProfileLog
        nlinarith
  · calc
      (d+j : ℝ)*probabilityProfileLipschitz ≤
          Real.exp (d+j : ℝ)*Real.exp probabilityProfileLipschitz :=
        mul_le_mul hn hk hκ (Real.exp_pos _).le
      _ = Real.exp ((d+j : ℝ)+probabilityProfileLipschitz) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (spatialProfileLog j d p) := by
        apply Real.exp_le_exp.mpr
        unfold spatialProfileLog
        nlinarith

noncomputable def spatialDiscretizationLog (j d : ℕ) (p l : ℝ) : ℝ :=
  let P := spatialProfileLog j d p
  2*(j : ℝ)^2+(2*j+4)*P+(j+2*d)*(P+4)+4+j*l

noncomputable def spatialDisplacementLog (j d e n : ℕ) (p : ℝ) : ℝ :=
  (j : ℝ)^2+(j+3)*spatialProfileLog j d p+2*e+n

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AnisotropicSpatialCapBudget
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

noncomputable def anisotropicSpatialDensityCap {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (κ : ℝ) : ℝ :=
  (Fintype.card (Unit ⊕ I)).factorial *
    (physicalSpatialInverseBound I κ) ^ Fintype.card (Unit ⊕ I) * 2 ^ Fintype.card (UnselectedColumn s)

noncomputable def anisotropicSpatialDensityLip {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (κ : ℝ) : ℝ :=
  anisotropicSpatialDensityCap s κ *
    ((Fintype.card (UnselectedColumn s) + Fintype.card (Unit ⊕ I) : ℝ) * probabilityProfileLipschitz) *
      physicalSpatialInverseBound I κ

theorem anisotropicSpatialDensityCap_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ anisotropicSpatialDensityCap s κ := by
  unfold anisotropicSpatialDensityCap physicalSpatialInverseBound
  positivity

theorem anisotropicSpatialDensityLip_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ anisotropicSpatialDensityLip s κ := by
  unfold anisotropicSpatialDensityLip anisotropicSpatialDensityCap physicalSpatialInverseBound
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AnisotropicTupleErrorChoice
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

theorem physicalSpatialInverseBound_eq_scalar (I : Type*) [Fintype I] (M : ℕ) :
    physicalSpatialInverseBound I (1 / (M : ℝ)) = scalarSpatialInverseAllowance I M := by
  simp [physicalSpatialInverseBound, scalarSpatialInverseAllowance, div_eq_mul_inv,
    Fintype.card_sum, Nat.add_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AnisotropicTupleChoiceBudget
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

noncomputable def anisotropicTupleEarlyBudget {I G : Type*} [Fintype I] [Fintype G]
    (N : Type*) [Fintype N] (s : I ↪ G) (p E : ℝ) : ℝ :=
  p + (p ^ 3 + anisotropicSpatialCapLog p) + (coefficientErrorVolumeLog p + 4) +
    spatialDisplacementLog (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s ⊕ N))
      (Fintype.card (UnselectedColumn s)) (Fintype.card N) p + E

theorem anisotropicTupleEarlyBudget_bounds {I G : Type*} [Fintype I] [Fintype G]
    (N : Type*) [Fintype N] (s : I ↪ G) {p E : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) :
    let Q := anisotropicTupleEarlyBudget N s p E
    0 ≤ Q ∧ p ≤ Q ∧ p ^ 3 + anisotropicSpatialCapLog p ≤ Q ∧
      coefficientErrorVolumeLog p + 4 ≤ Q ∧
      spatialDisplacementLog (Fintype.card (Unit ⊕ I)) (Fintype.card (UnselectedColumn s ⊕ N))
        (Fintype.card (UnselectedColumn s)) (Fintype.card N) p ≤ Q ∧ E ≤ Q := by
  have hcap : 0 ≤ p ^ 3 + anisotropicSpatialCapLog p := by
    have := anisotropicSpatialCapLog_nonneg hp
    positivity
  have hvol : 0 ≤ coefficientErrorVolumeLog p + 4 := by
    unfold coefficientErrorVolumeLog
    positivity
  have hdis : 0 ≤ spatialDisplacementLog (Fintype.card (Unit ⊕ I))
      (Fintype.card (UnselectedColumn s ⊕ N)) (Fintype.card (UnselectedColumn s))
      (Fintype.card N) p := by
    unfold spatialDisplacementLog spatialProfileLog
    positivity
  dsimp only [anisotropicTupleEarlyBudget]
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelScalarEnvelope
namespace OAI

section

namespace Erdos3

theorem kernelInverseEnvelope_nonneg {D p : ℝ} (hD : 0 ≤ D) (hp : 0 ≤ p) :
    0 ≤ kernelInverseEnvelope D p := by
  unfold kernelInverseEnvelope
  positivity

theorem kernelGeometryEnvelope_nonneg {D p : ℝ} (hD : 0 ≤ D) (hp : 0 ≤ p) :
    0 ≤ kernelGeometryEnvelope D p := by
  have hi := kernelInverseEnvelope_nonneg hD hp
  unfold kernelGeometryEnvelope
  positivity

theorem kernelOutputEnvelope_nonneg {D p : ℝ} (hD : 0 ≤ D) (hp : 0 ≤ p) :
    0 ≤ kernelOutputEnvelope D p := by
  have hg := kernelGeometryEnvelope_nonneg hD hp
  unfold kernelOutputEnvelope
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)] {D : ℝ}

theorem allocatedDensityEnvelope_nonneg (m : ℕ) {D p : ℝ} (hD : 0 ≤ D) (hp : 0 ≤ p) :
    0 ≤ allocatedDensityEnvelope m D p := by
  have ho := kernelOutputEnvelope_nonneg hD (show 0 ≤ 4*(p+8) by positivity)
  unfold allocatedDensityEnvelope
  positivity

theorem allocatedSupportEnvelope_nonneg (m : ℕ) {D p : ℝ} (hD : 0 ≤ D) (hp : 0 ≤ p) :
    0 ≤ allocatedSupportEnvelope m D p := by
  have hd := allocatedDensityEnvelope_nonneg m hD hp
  unfold allocatedSupportEnvelope
  positivity

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def comparisonProfileBound : ℕ := ⌈(probabilityProfileLipschitz : ℝ)⌉₊+1

noncomputable def allocatedComparisonDimension {A : Type*} [Semiring A] (m : ℕ) (p : A) : A :=
  (m+1 : ℕ)+p+((m+1 : ℕ)*(p+1)^(m+1)+1)+(2^(m+1) : ℕ)+
    (m+2 : ℕ)*p+(2*m : ℕ)*p+(2*m : ℕ)*p*(2^(m+1) : ℕ)+comparisonProfileBound

theorem allocatedComparisonDimension_bounds (m : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    let D := allocatedComparisonDimension m p
    0 ≤ D ∧ ((m+1 : ℕ) : ℝ) ≤ D ∧ p ≤ D ∧ ((2^(m+1) : ℕ) : ℝ) ≤ D ∧
      geometricSiteBudget m 0 p ≤ D ∧ ((m+2 : ℕ) : ℝ)*p ≤ D ∧
      ((2*m : ℕ) : ℝ)*p ≤ D ∧ ((2*m : ℕ) : ℝ)*p*(2^(m+1) : ℕ) ≤ D ∧
      (comparisonProfileBound : ℝ) ≤ D := by
  have hC : 0 ≤ ((m+1 : ℕ) : ℝ)*(p+1)^(m+1)+1 := by positivity
  have hpa : 0 ≤ ((m+2 : ℕ) : ℝ)*p := by positivity
  have ha : 0 ≤ ((2*m : ℕ) : ℝ)*p := by positivity
  have ho : 0 ≤ ((2*m : ℕ) : ℝ)*p*(2^(m+1) : ℕ) := by positivity
  have hm : (0 : ℝ) ≤ (m+1 : ℕ) := Nat.cast_nonneg _
  have hq : (0 : ℝ) ≤ (2^(m+1) : ℕ) := Nat.cast_nonneg _
  have hf : (0 : ℝ) ≤ comparisonProfileBound := Nat.cast_nonneg _
  dsimp only [allocatedComparisonDimension]
  simp only [geometricSiteBudget, pow_zero]
  push_cast at *
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedLocalResidueReconstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical Matrix

noncomputable def allocatedSpatialCoefficientCap {G : Type*} [Fintype G] {dim : ℕ}
    (X : Type*) [Fintype X] (selection : Fin dim ↪ G) (M modulus : ℕ) (mesh : ℝ) : ℝ :=
  ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
    (intervalSiteCount 4 mesh : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
    ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ)))) ^ Fintype.card X

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialNumericEnvelopeFunctoriality
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

noncomputable def anisotropicSpatialMeshLog (j d : ℕ) (p l : ℝ) : ℝ :=
  (j : ℝ) ^ 2 + j * l + 4 * (j + d) + spatialProfileLog j d p + 3

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem probabilityProfileLipschitz_le_comparisonProfileBound :
    (probabilityProfileLipschitz : ℝ) ≤ VectorPolynomial.comparisonProfileBound :=
  (Nat.le_ceil _).trans (by unfold VectorPolynomial.comparisonProfileBound; push_cast; linarith)

noncomputable def spatialFixedProfileEnvelope {A : Type*} [Semiring A] (p : A) : A :=
  (p + 1) * p + p ^ 2 + 4 * p + (VectorPolynomial.comparisonProfileBound : ℕ) + 1

noncomputable def spatialDisplacementEnvelope {A : Type*} [Semiring A] (p : A) : A :=
  p ^ 2 + (p + 3) * spatialFixedProfileEnvelope p + 2 * p + p

noncomputable def spatialDiscretizationEnvelope {A : Type*} [Semiring A] (p l : A) : A :=
  2 * p ^ 2 + (2 * p + 4) * spatialFixedProfileEnvelope p +
    (p + 2 * (2 * p)) * (spatialFixedProfileEnvelope p + 4) + 4 + p * l

noncomputable def spatialMeshEnvelope {A : Type*} [Semiring A] (p l : A) : A :=
  p ^ 2 + p * l + 4 * (p + 2 * p) + spatialFixedProfileEnvelope p + 3

noncomputable def spatialLipschitzEnvelope {A : Type*} [Semiring A] (p : A) : A :=
  anisotropicSpatialCapLog p + 2 * spatialFixedProfileEnvelope p

theorem spatialCostEnvelopes_nonneg {p l : ℝ} (hp : 0 ≤ p) (hl : 0 ≤ l) :
    0 ≤ spatialFixedProfileEnvelope p ∧ 0 ≤ spatialDisplacementEnvelope p ∧
      0 ≤ spatialDiscretizationEnvelope p l ∧ 0 ≤ spatialMeshEnvelope p l ∧
      0 ≤ spatialLipschitzEnvelope p := by
  dsimp only [spatialDisplacementEnvelope, spatialDiscretizationEnvelope,
    spatialMeshEnvelope, spatialLipschitzEnvelope, spatialFixedProfileEnvelope, anisotropicSpatialCapLog]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> positivity

theorem spatialProfileLog_le_fixedEnvelope (j d : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hj : (j : ℝ) ≤ p) (hd : (d : ℝ) ≤ 2 * p) :
    spatialProfileLog j d p ≤ spatialFixedProfileEnvelope p := by
  have hprofile := probabilityProfileLipschitz_le_comparisonProfileBound
  calc
    _ ≤ (p + 1) * p + p ^ 2 + 2 * p + 2 * p +
        (VectorPolynomial.comparisonProfileBound : ℝ) + 1 := by
      unfold spatialProfileLog
      gcongr
    _ = _ := by unfold spatialFixedProfileEnvelope; ring

theorem spatialDisplacementLog_le_envelope (j d e n : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hj : (j : ℝ) ≤ p) (hd : (d : ℝ) ≤ 2 * p)
    (he : (e : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) :
    spatialDisplacementLog j d e n p ≤ spatialDisplacementEnvelope p := by
  have hprofile := spatialProfileLog_le_fixedEnvelope j d hp hj hd
  have hprofile0 := spatialProfileLog_nonneg j d hp
  unfold spatialDisplacementLog spatialDisplacementEnvelope
  gcongr

theorem spatialDiscretizationLog_le_envelope (j d : ℕ) {p l : ℝ}
    (hp : 0 ≤ p) (hl : 0 ≤ l) (hj : (j : ℝ) ≤ p) (hd : (d : ℝ) ≤ 2 * p) :
    spatialDiscretizationLog j d p l ≤ spatialDiscretizationEnvelope p l := by
  have hprofile := spatialProfileLog_le_fixedEnvelope j d hp hj hd
  have hprofile0 := spatialProfileLog_nonneg j d hp
  dsimp only [spatialDiscretizationLog, spatialDiscretizationEnvelope]
  gcongr

theorem anisotropicSpatialMeshLog_le_envelope (j d : ℕ) {p l : ℝ}
    (hp : 0 ≤ p) (hl : 0 ≤ l) (hj : (j : ℝ) ≤ p) (hd : (d : ℝ) ≤ 2 * p) :
    anisotropicSpatialMeshLog j d p l ≤ spatialMeshEnvelope p l := by
  have hprofile := spatialProfileLog_le_fixedEnvelope j d hp hj hd
  unfold anisotropicSpatialMeshLog spatialMeshEnvelope
  gcongr

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

noncomputable def spatialLipschitzCostEnvelope {A : Type*} [Semiring A] (p l : A) : A :=
  p ^ 3 + spatialLipschitzEnvelope p + l + 1

theorem spatialAuxiliaryDimensions {I G N : Type*} [Fintype I] [Fintype G] [Fintype N]
    (s : I ↪ G) {p : ℝ} (hG : (Fintype.card G : ℝ) ≤ p) (hN : (Fintype.card N : ℝ) ≤ p) :
    (Fintype.card (UnselectedColumn s) : ℝ) ≤ p ∧
      (Fintype.card (UnselectedColumn s ⊕ N) : ℝ) ≤ 2 * p ∧
      (Fintype.card (Option (G ⊕ N)) : ℝ) ≤ 1 + 2 * p := by
  have he : (Fintype.card (UnselectedColumn s) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hG
  refine ⟨he, ?_, ?_⟩
  · simp only [Fintype.card_sum, Nat.cast_add]
    linarith
  · simp only [Fintype.card_option, Fintype.card_sum, Nat.cast_add, Nat.cast_one]
    linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedCoarseSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped NNReal

noncomputable def allocatedEarlyCoarseInput {A : Type*} [Semiring A] (m dim : ℕ) (s : A) : A :=
  let R := s + (m + dim + 2 : ℕ)
  2 * R + R ^ 3 + anisotropicSpatialCapLog R + spatialLipschitzEnvelope R +
    coefficientErrorVolumeLog R + 8

theorem allocatedEarlyCoarseInput_bounds (m dim : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    let R := s + (m + dim + 2 : ℕ)
    let T := allocatedEarlyCoarseInput m dim s
    0 ≤ T ∧ R ≤ T ∧ R ^ 3 ≤ T ∧
      R ^ 3 + anisotropicSpatialCapLog R ≤ T ∧
      R ^ 3 + spatialLipschitzEnvelope R + R ≤ T ∧
      coefficientErrorVolumeLog R + 4 ≤ T := by
  intro R T
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hcap := anisotropicSpatialCapLog_nonneg hR
  have hlip := (spatialCostEnvelopes_nonneg hR (le_refl (0 : ℝ))).2.2.2.2
  have hmass : 0 ≤ coefficientErrorVolumeLog R := by unfold coefficientErrorVolumeLog; positivity
  have hcube : 0 ≤ R ^ 3 := pow_nonneg hR _
  dsimp only [T, allocatedEarlyCoarseInput]
  change 0 ≤ 2 * R + R ^ 3 + anisotropicSpatialCapLog R + spatialLipschitzEnvelope R +
      coefficientErrorVolumeLog R + 8 ∧ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith only [hR, hcap, hlip, hmass, hcube]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCoverLogBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def allocatedIdealCoverPrimitiveLog {A : Type*} [Semiring A]
    (m : ℕ) (p c : A) : A :=
  8 * allocatedIdealCoverInputLog m (allocatedComparisonDimension m p) c + 14

noncomputable def allocatedIdealCoverPrimitiveRadius (m : ℕ) (p c : ℝ) : ℝ :=
  Real.exp (-allocatedIdealCoverPrimitiveLog m p c)

theorem allocatedIdealCoverPrimitiveRadius_bounds (m : ℕ) {p c : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) :
    0 ≤ allocatedIdealCoverPrimitiveLog m p c ∧
      0 < allocatedIdealCoverPrimitiveRadius m p c ∧
      allocatedIdealCoverPrimitiveRadius m p c ≤ 1 ∧
      (allocatedIdealCoverPrimitiveRadius m p c)⁻¹ = Real.exp (allocatedIdealCoverPrimitiveLog m p c) := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hL := (allocatedIdealCoverInputLog_bounds m hD hc).1
  have hlog : 0 ≤ allocatedIdealCoverPrimitiveLog m p c := by
    unfold allocatedIdealCoverPrimitiveLog
    positivity
  refine ⟨hlog, Real.exp_pos _, ?_, ?_⟩
  · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hlog)
  · simp only [allocatedIdealCoverPrimitiveRadius, Real.exp_neg, inv_inv]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

namespace VectorPolynomial

theorem allocatedComparisonDimension_mono (m : ℕ) {p p' : ℝ}
    (hp : 0 ≤ p) (hpp : p ≤ p') :
    allocatedComparisonDimension m p ≤ allocatedComparisonDimension m p' := by
  unfold allocatedComparisonDimension
  gcongr

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

noncomputable def allocatedSourceCoverRadiusLog {A : Type*} [Semiring A]
    (m : ℕ) (p c : A) : A := allocatedIdealCoverPrimitiveLog m p c + 1

noncomputable def allocatedSourceCoverRadius (m : ℕ) (p c : ℝ) : ℝ :=
  Real.exp (-allocatedSourceCoverRadiusLog m p c)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SharedWidthNormalizedTupleSideBudget
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

noncomputable def normalizedTupleLateBudget (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (p E l : ℝ) : ℝ :=
  let j := Fintype.card (Unit ⊕ Fin q)
  let d := Fintype.card (UnselectedColumn s ⊕ N)
  spatialDiscretizationLog j d p l + anisotropicSpatialMeshLog j d p l +
    (p ^ 3 + anisotropicSpatialCapLog p +
      2 * spatialProfileLog j (Fintype.card (UnselectedColumn s)) p + l + 1) +
    spatialTupleToleranceLog (anisotropicTupleEarlyBudget N s p (E + 3)) + E + 3 + 2 * l +
    Fintype.card (Option (G ⊕ N)) + Fintype.card (Option (G ⊕ N) × X) + Fintype.card N + 40

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

noncomputable def normalizedTupleWidthLog (N : Type*) [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (p E : ℝ) : ℝ :=
  let Q := anisotropicTupleEarlyBudget N s p (E + 3)
  2 * (Q + spatialTupleToleranceLog Q) + 4

noncomputable def normalizedTupleSideLog (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (p E l : ℝ) : ℝ :=
  3 * normalizedTupleLateBudget X N s p E l + normalizedTupleWidthLog N s p E + 3 * l + 17

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedTupleSideThreshold
namespace OAI

section

namespace Erdos3

noncomputable def tupleEarlyLogEnvelope {A : Type*} [Semiring A] (p E : A) : A :=
  p + (p ^ 3 + anisotropicSpatialCapLog p) + (coefficientErrorVolumeLog p + 4) +
    spatialDisplacementEnvelope p + E + 3

noncomputable def tupleWidthLogEnvelope {A : Type*} [Semiring A] (p E : A) : A :=
  2 * (tupleEarlyLogEnvelope p E + spatialTupleToleranceLog (tupleEarlyLogEnvelope p E)) + 4

noncomputable def tupleLateLogEnvelope {A : Type*} [Semiring A] (p E l : A) : A :=
  spatialDiscretizationEnvelope p l + spatialMeshEnvelope p l + spatialLipschitzCostEnvelope p l +
    spatialTupleToleranceLog (tupleEarlyLogEnvelope p E) + E + 3 + 2 * l +
    (1 + 2 * p) + (1 + 2 * p) * p + p + 40

noncomputable def tupleSideLogEnvelope {A : Type*} [Semiring A] (p E l : A) : A :=
  3 * tupleLateLogEnvelope p E l + tupleWidthLogEnvelope p E + 3 * l + 17

theorem normalizedTuple_log_envelopes (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) {p E l : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l)
    (hq : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hN : (Fintype.card N : ℝ) ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) :
    normalizedTupleWidthLog N s p E ≤ tupleWidthLogEnvelope p E ∧
      normalizedTupleSideLog X N s p E l ≤ tupleSideLogEnvelope p E l := by
  obtain ⟨he, hd, hcoords⟩ := spatialAuxiliaryDimensions (N := N) s hG hN
  have hdis := spatialDisplacementLog_le_envelope _ _ _ _ hp hq hd he hN
  have hearly : anisotropicTupleEarlyBudget N s p (E + 3) ≤ tupleEarlyLogEnvelope p E := by
    unfold anisotropicTupleEarlyBudget tupleEarlyLogEnvelope
    linarith
  have hearly0 := (anisotropicTupleEarlyBudget_bounds N s hp (by linarith : 0 ≤ E + 3)).1
  have ht : spatialTupleToleranceLog (anisotropicTupleEarlyBudget N s p (E + 3)) ≤
      spatialTupleToleranceLog (tupleEarlyLogEnvelope p E) := by
    unfold spatialTupleToleranceLog
    gcongr
  have hw : normalizedTupleWidthLog N s p E ≤ tupleWidthLogEnvelope p E := by
    unfold normalizedTupleWidthLog tupleWidthLogEnvelope
    linarith
  have hA := spatialDiscretizationLog_le_envelope _ _ hp hl hq hd
  have hT := anisotropicSpatialMeshLog_le_envelope _ _ hp hl hq hd
  have hprof := spatialProfileLog_le_fixedEnvelope _ _ hp hq (he.trans (by linarith))
  have hK : p ^ 3 + anisotropicSpatialCapLog p +
      2 * spatialProfileLog (Fintype.card (Unit ⊕ Fin q)) (Fintype.card (UnselectedColumn s)) p + l + 1 ≤
        spatialLipschitzCostEnvelope p l := by
    unfold spatialLipschitzCostEnvelope spatialLipschitzEnvelope
    linarith
  have hprod : (Fintype.card (Option (G ⊕ N) × X) : ℝ) ≤ (1 + 2 * p) * p := by
    simp only [Fintype.card_prod, Nat.cast_mul]
    exact mul_le_mul hcoords hX (Nat.cast_nonneg _) (by positivity)
  have hlate : normalizedTupleLateBudget X N s p E l ≤ tupleLateLogEnvelope p E l := by
    unfold normalizedTupleLateBudget tupleLateLogEnvelope
    linarith
  refine ⟨hw, ?_⟩
  unfold normalizedTupleSideLog tupleSideLogEnvelope
  linarith

theorem tupleSideLogEnvelope_mono {p E l P F L : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l) (hP : p ≤ P) (hF : E ≤ F) (hL : l ≤ L) :
    tupleSideLogEnvelope p E l ≤ tupleSideLogEnvelope P F L := by
  have hP0 : 0 ≤ P := hp.trans hP
  dsimp only [tupleEarlyLogEnvelope, tupleWidthLogEnvelope, tupleLateLogEnvelope, tupleSideLogEnvelope,
    spatialTupleToleranceLog, spatialDiscretizationEnvelope, spatialMeshEnvelope,
    spatialLipschitzCostEnvelope, spatialLipschitzEnvelope, spatialDisplacementEnvelope,
    spatialFixedProfileEnvelope, anisotropicSpatialCapLog, coefficientErrorVolumeLog]
  gcongr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedModularCanonicalDetectorResourceBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

namespace PreparedModularCanonicalDetectorResources

def toList {α : Type*} (r : PreparedModularCanonicalDetectorResources α) : List α :=
  [r.Q, r.v, r.w, r.Dg, r.Pproj, r.coverLog, r.Pmass, r.Vlog, r.Nlog, r.Pbox, r.Banalytic, r.baseAmbient, r.tq, r.pq, r.gridlog, r.Fpref, r.sumlog, r.idealQ, r.ambient, r.Psample, r.Pside, r.Pnative, r.nativeBudget, r.E, r.full, r.required]

def total {α : Type*} [AddMonoid α] (r : PreparedModularCanonicalDetectorResources α) : α :=
  r.toList.sum

def map {α β : Type*} (f : α → β) (r : PreparedModularCanonicalDetectorResources α) :
    PreparedModularCanonicalDetectorResources β :=
  { Q := f r.Q,
    v := f r.v,
    w := f r.w,
    Dg := f r.Dg,
    Pproj := f r.Pproj,
    coverLog := f r.coverLog,
    Pmass := f r.Pmass,
    Vlog := f r.Vlog,
    Nlog := f r.Nlog,
    Pbox := f r.Pbox,
    Banalytic := f r.Banalytic,
    baseAmbient := f r.baseAmbient,
    tq := f r.tq,
    pq := f r.pq,
    gridlog := f r.gridlog,
    Fpref := f r.Fpref,
    sumlog := f r.sumlog,
    idealQ := f r.idealQ,
    ambient := f r.ambient,
    Psample := f r.Psample,
    Pside := f r.Pside,
    Pnative := f r.Pnative,
    nativeBudget := f r.nativeBudget,
    E := f r.E,
    full := f r.full,
    required := f r.required }

end PreparedModularCanonicalDetectorResources

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularGeneralDetectorNativeBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem generalResources_total_map {α β : Type*} [Semiring α] [Semiring β]
    (f : α →+* β) (r : PreparedModularCanonicalDetectorResources α) :
    (r.map f).total = f r.total := by
  simp [PreparedModularCanonicalDetectorResources.total,
    PreparedModularCanonicalDetectorResources.toList,
    PreparedModularCanonicalDetectorResources.map]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteForwardTreeStorage
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem allocatedCandidateForwardControlInput_denominator_bound
    (s d q : ℕ) {b x cumulative : ℝ}
    (hb : 0 ≤ b) (hxb : x ≤ b) (hcb : cumulative ≤ b)
    (hq : (q : ℝ) ≤ Real.exp x) :
    (q : ℝ) * Real.exp ((s : ℝ) * (d : ℝ) * cumulative) ≤
      Real.exp (allocatedCandidateForwardControlInput s d b) := by
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hfactor : (s : ℝ) * d + 1 ≤ ((s : ℝ) + 3) * ((d : ℝ) + 1) := by
    nlinarith only [hs, hd]
  have hexponent : x + (s : ℝ) * d * cumulative ≤
      allocatedCandidateForwardControlInput s d b := by
    calc
      x + (s : ℝ) * d * cumulative ≤ b + (s : ℝ) * d * b :=
        add_le_add hxb (mul_le_mul_of_nonneg_left hcb (mul_nonneg hs hd))
      _ = ((s : ℝ) * d + 1) * b := by ring
      _ ≤ (((s : ℝ) + 3) * ((d : ℝ) + 1)) * b :=
        mul_le_mul_of_nonneg_right hfactor hb
      _ ≤ (((s : ℝ) + 3) * ((d : ℝ) + 1)) * (b + 1) :=
        mul_le_mul_of_nonneg_left (by linarith only) (by positivity)
      _ = allocatedCandidateForwardControlInput s d b := rfl
  calc
    (q : ℝ) * Real.exp ((s : ℝ) * d * cumulative) ≤
        Real.exp x * Real.exp ((s : ℝ) * d * cumulative) :=
      mul_le_mul_of_nonneg_right hq (Real.exp_nonneg _)
    _ = Real.exp (x + (s : ℝ) * d * cumulative) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hexponent

theorem allocatedCandidateForwardControlInput_cost_bound
    (s d : ℕ) {b x cumulative Bbound : ℝ}
    (hxb : x ≤ b) (hcb : cumulative ≤ b) (hd : (d : ℝ) ≤ x)
    (hBbound : Bbound ≤ Real.exp x) :
    (d : ℝ) * Bbound * Real.exp cumulative ≤
      Real.exp (allocatedCandidateForwardControlInput s d b + 2) := by
  have hx : 0 ≤ x := (Nat.cast_nonneg d).trans hd
  have hb : 0 ≤ b := hx.trans hxb
  have hdexp : (d : ℝ) ≤ Real.exp x :=
    hd.trans (by linarith only [Real.add_one_le_exp x])
  have hthree := (allocatedCandidateForwardControlInput_bounds s d hb).2.2
  calc
    (d : ℝ) * Bbound * Real.exp cumulative ≤
        (d : ℝ) * Real.exp x * Real.exp cumulative :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hBbound (Nat.cast_nonneg d)) (Real.exp_nonneg _)
    _ ≤ Real.exp x * Real.exp x * Real.exp cumulative :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hdexp (Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ = Real.exp (x + x + cumulative) := by rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (allocatedCandidateForwardControlInput s d b + 2) :=
      Real.exp_le_exp.mpr (by linarith only [hxb, hcb, hthree])

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCandidateCommonFastGeometry
namespace OAI

section

namespace Erdos3

open Module
open scoped Classical TensorProduct

def allocatedCandidateCommonFastBudget (s : ℕ) (p : ℝ) : ℝ :=
  allocatedCandidateCommonFastGeometryLog p +
    NilpotentLieFiltration.pointwiseFastSectionInput s p

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedProductChartRadius
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

theorem allocatedProductChartLog_bounds (m : ℕ) {D c : ℝ} (hD : 0 ≤ D) (hc : 0 ≤ c) :
    let H := 8 * allocatedIdealCoverInputLog m D c + 14
    let F := H + 2 * D + 2
    0 ≤ H ∧ 0 ≤ F ∧ 2 * D ≤ F ∧ D ≤ F ∧ c ≤ F ∧
      H + 1 ≤ allocatedProductChartLog m D c ∧ 0 ≤ allocatedProductChartLog m D c := by
  obtain ⟨hL, _, _, _, _, hcL⟩ := allocatedIdealCoverInputLog_bounds m hD hc
  dsimp only [allocatedProductChartLog]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem allocatedProductChartRadius_bounds (m : ℕ) {D c : ℝ} (hD : 0 ≤ D) (hc : 0 ≤ c) :
    0 < allocatedProductChartRadius m D c ∧ allocatedProductChartRadius m D c ≤ 1 ∧
      (allocatedProductChartRadius m D c)⁻¹ = Real.exp (allocatedProductChartLog m D c) ∧
      allocatedProductChartRadius m D c ≤
        Real.exp (-(8 * allocatedIdealCoverInputLog m D c + 14 + 1)) := by
  obtain ⟨_, _, _, _, _, hHQ, hQ⟩ := allocatedProductChartLog_bounds m hD hc
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hQ), ?_, ?_⟩
  · simp only [allocatedProductChartRadius, Real.exp_neg, inv_inv]
  · exact Real.exp_le_exp.mpr (neg_le_neg hHQ)

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedUniformEarlyRadiusWithCutoff
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedBufferedRadiusInput {A : Type*} [Semiring A] (m : ℕ) (p g : A) : A :=
  allocatedComparisonDimension m p + g + ((2 * m + 5) * (m + 1) + 5 : ℕ)

noncomputable def allocatedBufferedRadiusLog {A : Type*} [Semiring A] (m : ℕ) (p g : A) : A :=
  (m + 10 : ℕ) * (allocatedBufferedRadiusInput m p g + (m + 3 : ℕ))

noncomputable def allocatedCommonRadiusLog {A : Type*} [Semiring A]
    (m : ℕ) (p g : A) : A :=
  allocatedBufferedRadiusLog m p g + allocatedIdealCoverPrimitiveLog m p g

noncomputable def allocatedCommonRadius (m : ℕ) (p g : ℝ) : ℝ :=
  Real.exp (-allocatedCommonRadiusLog m p g)

theorem allocatedBufferedRadiusInput_bounds (m : ℕ) {p g : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) :
    let P := allocatedBufferedRadiusInput m p g
    0 ≤ P ∧ allocatedComparisonDimension m p ≤ P ∧ g ≤ P ∧
      (((2 * m + 5) * (m + 1) + 5 : ℕ) : ℝ) ≤ P := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  dsimp only [allocatedBufferedRadiusInput]
  have ha : (0 : ℝ) ≤ ((2 * m + 5) * (m + 1) + 5 : ℕ) := Nat.cast_nonneg _
  constructor
  · positivity
  constructor
  · linarith
  constructor <;> linarith

theorem allocatedCommonRadiusLog_bounds (m : ℕ) {p g : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) :
    0 ≤ allocatedCommonRadiusLog m p g ∧
      allocatedBufferedRadiusLog m p g ≤ allocatedCommonRadiusLog m p g ∧
      allocatedIdealCoverPrimitiveLog m p g ≤ allocatedCommonRadiusLog m p g := by
  have hP := (allocatedBufferedRadiusInput_bounds m hp hg).1
  have hb : 0 ≤ allocatedBufferedRadiusLog m p g := by
    unfold allocatedBufferedRadiusLog
    positivity
  have hi := (allocatedIdealCoverPrimitiveRadius_bounds m hp hg).1
  dsimp only [allocatedCommonRadiusLog]
  exact ⟨add_nonneg hb hi, le_add_of_nonneg_right hi, le_add_of_nonneg_left hb⟩

theorem allocatedCommonRadiusLog_mono (m : ℕ) {p g p' g' : ℝ}
    (hp : 0 ≤ p) (_hg : 0 ≤ g) (hpp : p ≤ p') (hgg : g ≤ g') :
    allocatedCommonRadiusLog m p g ≤ allocatedCommonRadiusLog m p' g' := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hDD := allocatedComparisonDimension_mono m hp hpp
  unfold allocatedCommonRadiusLog allocatedBufferedRadiusLog allocatedBufferedRadiusInput
    allocatedIdealCoverPrimitiveLog allocatedIdealCoverInputLog allocatedSiteCoefficientLog
  gcongr

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedCommonProductRadiusLog {A : Type*} [Semiring A]
    (m : ℕ) (p g : A) : A :=
  allocatedCommonRadiusLog m p g +
    allocatedProductChartLog m (allocatedComparisonDimension m p) g

noncomputable def allocatedCommonProductRadius (m : ℕ) (p g : ℝ) : ℝ :=
  Real.exp (-allocatedCommonProductRadiusLog m p g)

theorem allocatedCommonProductRadius_bounds (m : ℕ) {p g : ℝ} (hp : 0 ≤ p) (hg : 0 ≤ g) :
    0 ≤ allocatedCommonProductRadiusLog m p g ∧
      0 < allocatedCommonProductRadius m p g ∧ allocatedCommonProductRadius m p g ≤ 1 ∧
      (allocatedCommonProductRadius m p g)⁻¹ = Real.exp (allocatedCommonProductRadiusLog m p g) ∧
      allocatedCommonProductRadius m p g ≤ allocatedCommonRadius m p g ∧
      allocatedCommonProductRadius m p g ≤
        allocatedProductChartRadius m (allocatedComparisonDimension m p) g ∧
      allocatedCommonProductRadius m p g ≤ allocatedSourceCoverRadius m p g := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hcommon := (allocatedCommonRadiusLog_bounds m hp hg).1
  have hproduct := (allocatedProductChartLog_bounds m hD hg).2.2.2.2.2.2
  have hlog : 0 ≤ allocatedCommonProductRadiusLog m p g := add_nonneg hcommon hproduct
  have hc : allocatedCommonProductRadius m p g ≤ allocatedCommonRadius m p g :=
    Real.exp_le_exp.mpr (neg_le_neg (le_add_of_nonneg_right hproduct))
  have hp' : allocatedCommonProductRadius m p g ≤
      allocatedProductChartRadius m (allocatedComparisonDimension m p) g :=
    Real.exp_le_exp.mpr (neg_le_neg (le_add_of_nonneg_left hcommon))
  refine ⟨hlog, Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hlog), ?_, hc, hp', ?_⟩
  · simp only [allocatedCommonProductRadius, Real.exp_neg, inv_inv]
  · exact hp'.trans (allocatedProductChartRadius_bounds m hD hg).2.2.2

theorem allocatedCommonProductRadiusLog_mono (m : ℕ) {p g p' g' : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) (hpp : p ≤ p') (hgg : g ≤ g') :
    allocatedCommonProductRadiusLog m p g ≤ allocatedCommonProductRadiusLog m p' g' := by
  exact add_le_add (allocatedCommonRadiusLog_mono m hp hg hpp hgg)
    (allocatedProductChartLog_mono m (allocatedComparisonDimension_bounds m hp).1
      (allocatedComparisonDimension_mono m hp hpp) hgg)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NormalizedTupleLargerBudget
namespace OAI

section

namespace Erdos3

theorem normalizedTuple_log_mono (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G)
    {p E l P F L : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l)
    (hpP : p ≤ P) (hEF : E ≤ F) (hlL : l ≤ L) :
    normalizedTupleWidthLog N s p E ≤ normalizedTupleWidthLog N s P F ∧
      normalizedTupleSideLog X N s p E l ≤ normalizedTupleSideLog X N s P F L := by
  have hP := hp.trans hpP
  have hF := hE.trans hEF
  have hL := hl.trans hlL
  constructor
  · dsimp only [normalizedTupleWidthLog, anisotropicTupleEarlyBudget, spatialTupleToleranceLog,
      spatialDisplacementLog, spatialProfileLog, anisotropicSpatialCapLog, coefficientErrorVolumeLog]
    gcongr
  · dsimp only [normalizedTupleSideLog, normalizedTupleLateBudget, normalizedTupleWidthLog,
      anisotropicTupleEarlyBudget, spatialTupleToleranceLog, spatialDiscretizationLog,
      anisotropicSpatialMeshLog, spatialDisplacementLog, spatialProfileLog,
      anisotropicSpatialCapLog, coefficientErrorVolumeLog]
    gcongr

theorem normalizedTuple_log_envelopes_of_le (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G)
    {p E l P : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l) (hpP : p ≤ P)
    (hq : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ P)
    (hG : (Fintype.card G : ℝ) ≤ P) (hN : (Fintype.card N : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P) :
    normalizedTupleWidthLog N s p E ≤ tupleWidthLogEnvelope P E ∧
      normalizedTupleSideLog X N s p E l ≤ tupleSideLogEnvelope P E l := by
  obtain ⟨hwidth, hside⟩ := normalizedTuple_log_mono X N s hp hE hl hpP le_rfl le_rfl
  obtain ⟨hwidth', hside'⟩ := normalizedTuple_log_envelopes X N s (hp.trans hpP) hE hl hq hG hN hX
  exact ⟨hwidth.trans hwidth', hside.trans hside'⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineScaleEnvelope
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

 theorem allocatedAffineL1Log_nonneg (m : ℕ) {D P Prho Pk : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hr : 0 ≤ Prho) (hk : 0 ≤ Pk) :
    0 ≤ allocatedAffineL1Log m D P Prho Pk := by
  have hd := allocatedDensityEnvelope_nonneg m hD hP
  have hs := allocatedSupportEnvelope_nonneg m hD hP
  dsimp only [allocatedAffineL1Log, allocatedIdealLipEnvelope, scalarCubeRiemannLog]
  positivity

 theorem allocatedAffineLengthLog_bounds (m : ℕ) {D P Prho Pk target F T : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hr : 0 ≤ Prho) (hk : 0 ≤ Pk)
    (ht : 0 ≤ target) (hF : 0 ≤ F) (hT : 0 ≤ T) :
    let e := allocatedAffineCoefficientAccuracyLog m D P Prho Pk target
    let E := allocatedAffineReferenceAccuracyLog m D P Prho Pk target
    let L := allocatedAffineLengthLog m D P Prho Pk target F T
    0 ≤ e ∧ 0 ≤ E ∧ 0 ≤ L ∧ E ≤ L ∧
      (m : ℝ) * allocatedFrontEnvelope m D P e ≤ L ∧
      progressionSliceLengthLog D E F T ≤ L := by
  intro e E L
  have hb := allocatedAffineL1Log_nonneg m hD hP hr hk
  have he : 0 ≤ e := by dsimp [e, allocatedAffineCoefficientAccuracyLog, coefficientReplacementErrorLog]; positivity
  have hE : 0 ≤ E := by dsimp [E, allocatedAffineReferenceAccuracyLog, affineReferenceCoefficientLog]; positivity
  have hki := kernelInverseEnvelope_nonneg hD hP
  have hf : 0 ≤ (m : ℝ) * allocatedFrontEnvelope m D P e := by
    dsimp [allocatedFrontEnvelope, allocatedKernelEnvelope]; positivity
  have hs : 0 ≤ progressionSliceLengthLog D E F T := by
    dsimp [progressionSliceLengthLog, scalarCubeRiemannLog]; positivity
  have hEL : E ≤ progressionSliceLengthLog D E F T := by
    have hB : 0 ≤ scalarCubeRiemannLog D := by unfold scalarCubeRiemannLog; positivity
    dsimp only [progressionSliceLengthLog]; linarith
  refine ⟨he, hE, add_nonneg hf hs, ?_, le_add_of_nonneg_right hs, le_add_of_nonneg_left hf⟩
  exact hEL.trans (le_add_of_nonneg_left hf)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedAffineScalePolynomial {A : Type*} [Semiring A]
    (m : ℕ) (D P Lb target F T : A) : A :=
  let e := target + 1 + coefficientReplacementErrorLog D Lb
  let E := target + 1 + affineReferenceCoefficientLog D Lb + 4
  let Q := D + P + (m * allocatedFrontEnvelope m D P e + progressionSliceLengthLog D E F T) + 1
  (1 + Q ^ 2) * (5 * Q + 49)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PartitionedAffineLogEnvelope
namespace OAI

section

namespace Erdos3

section Definitions
variable {A : Type*} [Semiring A]
def affineMinorConstantEnvelope (D : A) : A :=
  D * D * (D + 1)^2 + 3 * affineMinorVariableEnvelope D +
    (affineMinorDegreeEnvelope D + 1) +
    affineMinorDegreeEnvelope D * (8 + (affineMinorDegreeEnvelope D + 1))
def affineMinorLogEnvelope (D P E F : A) : A :=
  affineMinorVariableEnvelope D * affineMinorDegreeEnvelope D + D * P + 2 +
    affineMinorVariableEnvelope D * affineMinorDegreeEnvelope D *
      (affineMinorConstantEnvelope D + 1 + E + 2) +
    affineMinorVariableEnvelope D * affineMinorDegreeEnvelope D * affineMinorVariableEnvelope D * F
end Definitions

 theorem affineMinorVariableEnvelope_nonneg {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ affineMinorVariableEnvelope D := by unfold affineMinorVariableEnvelope; positivity
 theorem affineMinorDegreeEnvelope_nonneg {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ affineMinorDegreeEnvelope D := by unfold affineMinorDegreeEnvelope; positivity
 theorem affineMinorConstantEnvelope_nonneg {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ affineMinorConstantEnvelope D := by
  have := affineMinorVariableEnvelope_nonneg hD
  have := affineMinorDegreeEnvelope_nonneg hD
  unfold affineMinorConstantEnvelope
  positivity
 theorem affineMinorLogEnvelope_nonneg {D P E F : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    0 ≤ affineMinorLogEnvelope D P E F := by
  have := affineMinorVariableEnvelope_nonneg hD
  have := affineMinorDegreeEnvelope_nonneg hD
  have := affineMinorConstantEnvelope_nonneg hD
  unfold affineMinorLogEnvelope
  positivity

end Erdos3

end

section

namespace Erdos3

section Definitions
variable {A : Type*} [Semiring A]
def affineInverseAxisEnvelope (D P E F : A) : A :=
  F + (D + D^2 + D * (P + D + D * D) + affineMinorLogEnvelope D P E F)

def affineDerivativeAxisEnvelope (D P : A) : A :=
  affineMinorVariableEnvelope D + D + (P + 2 * D + D * D)

def affineWeightAxisEnvelope (D P E F : A) : A :=
  (P + 3 * D + 1 + ((D + 1)^2 + 2 * D + 2) + 2 * (D * D) + E + 1) +
    (affineMinorVariableEnvelope D + P + affineMinorLogEnvelope D P E F +
      (affineMinorVariableEnvelope D + D^2 + D + (P + 2 * D + D * D) +
        D * (P + D + D * D + 1))) + 1
end Definitions

 theorem affineInverseAxisEnvelope_nonneg {D P E F : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    0 ≤ affineInverseAxisEnvelope D P E F := by
  have := affineMinorLogEnvelope_nonneg hD hP hE hF
  unfold affineInverseAxisEnvelope
  positivity
 theorem affineDerivativeAxisEnvelope_nonneg {D P : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) :
    0 ≤ affineDerivativeAxisEnvelope D P := by
  have := affineMinorVariableEnvelope_nonneg hD
  unfold affineDerivativeAxisEnvelope
  positivity
 theorem affineWeightAxisEnvelope_nonneg {D P E F : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    0 ≤ affineWeightAxisEnvelope D P E F := by
  have := affineMinorLogEnvelope_nonneg hD hP hE hF
  have := affineMinorVariableEnvelope_nonneg hD
  unfold affineWeightAxisEnvelope
  positivity

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

section Definitions
variable {A : Type*} [Semiring A]
def jointAffineInverseEnvelope (D P E F : A) : A := D + D * affineInverseAxisEnvelope D P E F
def jointAffineDerivativeEnvelope (D P : A) : A := D + D * affineDerivativeAxisEnvelope D P
def jointAffineWeightEnvelope (D P E F : A) : A := D + D * affineWeightAxisEnvelope D P E F
def jointAffineSourceEnvelope (D P E F : A) : A :=
  let out := D * D
  let param := D * affineMinorVariableEnvelope D
  let inv := jointAffineInverseEnvelope D P E F
  let deriv := jointAffineDerivativeEnvelope D P
  let weight := jointAffineWeightEnvelope D P E F
  (out + param + 3 * inv + deriv + weight + 1) +
    (param + 3 * inv + deriv + weight + 6) + inv + out + E + 4
end Definitions

variable {ι α : Type*} [Fintype ι] [Fintype α]
  {B O : ι → Type*} [∀ i, Fintype (B i)] [∀ i, Fintype (O i)]

 theorem jointAffineSourceEnvelope_nonneg {D P E F : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    0 ≤ jointAffineSourceEnvelope D P E F := by
  have := affineMinorVariableEnvelope_nonneg hD
  have := affineInverseAxisEnvelope_nonneg hD hP hE hF
  have := affineDerivativeAxisEnvelope_nonneg hD hP
  have := affineWeightAxisEnvelope_nonneg hD hP hE hF
  unfold jointAffineSourceEnvelope jointAffineInverseEnvelope jointAffineDerivativeEnvelope jointAffineWeightEnvelope
  positivity

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal Classical

section Definitions
variable {A : Type*} [Semiring A]
def affineProfileInputEnvelope (D A₀ T₀ E F : A) : A :=
  jointAffineSourceEnvelope D (affineProfileCoefficientEnvelope D A₀ T₀) (E + D + 4) F

def affineProfileToleranceEnvelope (degree : ℕ) (D N A₀ T₀ E F : A) : A :=
  16 + 6 * affineProfileInputEnvelope D A₀ T₀ E F +
    (3 * N * (degree + 2 : ℕ) +
      (2 * (D + affineProfileCoefficientEnvelope D A₀ T₀ + degree * D) + 1)) + 1
end Definitions

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InitializedEarlyCanonicalSliceScales
namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

noncomputable def canonicalSublevelCutoffLip : ℝ≥0 :=
  Classical.choose exists_smooth_sublevel_cutoff

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteScheduleGeometryBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

theorem canonical_minorVariable_mono {D D' : ℝ} (hD0 : 0 ≤ D) (hD : D ≤ D') :
    affineMinorVariableEnvelope D ≤ affineMinorVariableEnvelope D' := by
  have hD'0 := hD0.trans hD
  dsimp only [affineMinorVariableEnvelope]
  gcongr

theorem canonical_minorDegree_mono {D D' : ℝ} (hD0 : 0 ≤ D) (hD : D ≤ D') :
    affineMinorDegreeEnvelope D ≤ affineMinorDegreeEnvelope D' := by
  have hD'0 := hD0.trans hD
  dsimp only [affineMinorDegreeEnvelope]
  gcongr

theorem canonical_minorConstant_mono {D D' : ℝ} (hD0 : 0 ≤ D) (hD : D ≤ D') :
    affineMinorConstantEnvelope D ≤ affineMinorConstantEnvelope D' := by
  have hD'0 := hD0.trans hD
  have hv := canonical_minorVariable_mono hD0 hD
  have hd := canonical_minorDegree_mono hD0 hD
  have hd0 := affineMinorDegreeEnvelope_nonneg hD0
  have hd'0 := affineMinorDegreeEnvelope_nonneg hD'0
  dsimp only [affineMinorConstantEnvelope]
  gcongr

theorem canonical_minorLog_mono {D D' P P' E E' F F' : ℝ}
    (hD0 : 0 ≤ D) (hP0 : 0 ≤ P) (hE0 : 0 ≤ E) (hF0 : 0 ≤ F)
    (hD : D ≤ D') (hP : P ≤ P') (hE : E ≤ E') (hF : F ≤ F') :
    affineMinorLogEnvelope D P E F ≤ affineMinorLogEnvelope D' P' E' F' := by
  have hD'0 := hD0.trans hD
  have hv := canonical_minorVariable_mono hD0 hD
  have hd := canonical_minorDegree_mono hD0 hD
  have hc := canonical_minorConstant_mono hD0 hD
  have hv0 := affineMinorVariableEnvelope_nonneg hD0
  have hv'0 := affineMinorVariableEnvelope_nonneg hD'0
  have hd0 := affineMinorDegreeEnvelope_nonneg hD0
  have hd'0 := affineMinorDegreeEnvelope_nonneg hD'0
  have hc0 := affineMinorConstantEnvelope_nonneg hD0
  dsimp only [affineMinorLogEnvelope]
  gcongr

theorem canonical_inverseAxis_mono {D D' P P' E E' F F' : ℝ}
    (hD0 : 0 ≤ D) (hP0 : 0 ≤ P) (hE0 : 0 ≤ E) (hF0 : 0 ≤ F)
    (hD : D ≤ D') (hP : P ≤ P') (hE : E ≤ E') (hF : F ≤ F') :
    affineInverseAxisEnvelope D P E F ≤ affineInverseAxisEnvelope D' P' E' F' := by
  have hD'0 := hD0.trans hD
  have hm := canonical_minorLog_mono hD0 hP0 hE0 hF0 hD hP hE hF
  dsimp only [affineInverseAxisEnvelope]
  gcongr

theorem canonical_derivativeAxis_mono {D D' P P' : ℝ}
    (hD0 : 0 ≤ D) (hD : D ≤ D') (hP : P ≤ P') :
    affineDerivativeAxisEnvelope D P ≤ affineDerivativeAxisEnvelope D' P' := by
  have hD'0 := hD0.trans hD
  have hv := canonical_minorVariable_mono hD0 hD
  dsimp only [affineDerivativeAxisEnvelope]
  gcongr

theorem canonical_weightAxis_mono {D D' P P' E E' F F' : ℝ}
    (hD0 : 0 ≤ D) (hP0 : 0 ≤ P) (hE0 : 0 ≤ E) (hF0 : 0 ≤ F)
    (hD : D ≤ D') (hP : P ≤ P') (hE : E ≤ E') (hF : F ≤ F') :
    affineWeightAxisEnvelope D P E F ≤ affineWeightAxisEnvelope D' P' E' F' := by
  have hD'0 := hD0.trans hD
  have hv := canonical_minorVariable_mono hD0 hD
  have hm := canonical_minorLog_mono hD0 hP0 hE0 hF0 hD hP hE hF
  dsimp only [affineWeightAxisEnvelope]
  gcongr

theorem canonical_jointSource_mono {D D' P P' E E' F F' : ℝ}
    (hD0 : 0 ≤ D) (hP0 : 0 ≤ P) (hE0 : 0 ≤ E) (hF0 : 0 ≤ F)
    (hD : D ≤ D') (hP : P ≤ P') (hE : E ≤ E') (hF : F ≤ F') :
    jointAffineSourceEnvelope D P E F ≤ jointAffineSourceEnvelope D' P' E' F' := by
  have hD'0 := hD0.trans hD
  have hv := canonical_minorVariable_mono hD0 hD
  have hi := canonical_inverseAxis_mono hD0 hP0 hE0 hF0 hD hP hE hF
  have hd := canonical_derivativeAxis_mono hD0 hD hP
  have hw := canonical_weightAxis_mono hD0 hP0 hE0 hF0 hD hP hE hF
  have hv0 := affineMinorVariableEnvelope_nonneg hD0
  have hi0 := affineInverseAxisEnvelope_nonneg hD0 hP0 hE0 hF0
  have hd0 := affineDerivativeAxisEnvelope_nonneg hD0 hP0
  have hw0 := affineWeightAxisEnvelope_nonneg hD0 hP0 hE0 hF0
  dsimp only [jointAffineSourceEnvelope, jointAffineInverseEnvelope,
    jointAffineDerivativeEnvelope, jointAffineWeightEnvelope]
  gcongr

theorem canonical_profileInput_mono {D D' A A' T T' E E' F F' : ℝ}
    (hD0 : 0 ≤ D) (hA0 : 0 ≤ A) (hT0 : 0 ≤ T) (hE0 : 0 ≤ E) (hF0 : 0 ≤ F)
    (hD : D ≤ D') (hA : A ≤ A') (hT : T ≤ T') (hE : E ≤ E') (hF : F ≤ F') :
    affineProfileInputEnvelope D A T E F ≤ affineProfileInputEnvelope D' A' T' E' F' := by
  have hD'0 := hD0.trans hD
  apply canonical_jointSource_mono hD0
    (by dsimp only [affineProfileCoefficientEnvelope]; positivity) (by positivity) hF0 hD
  · dsimp only [affineProfileCoefficientEnvelope]; gcongr
  · gcongr
  · exact hF

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedCanonicalProjectionBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

noncomputable def canonicalProjectionRowCost (m dim : ℕ) : ℕ :=
  Fintype.card (Finset (Fin dim)) *
    ∑ j : Fin m, Fintype.card (BoundedBooleanJet (Fin dim) (j.val + 1))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RealMatrixSpecifiedGrid
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] in

theorem real_matrix_specified_denominator_grid (M : Matrix ι κ ℝ) (D l : ℕ)
    (hM : ∀ i j, ∃ z : ℤ, (D : ℝ) * M i j = z)
    (x : κ → ℝ) (hx : x ∈ realDenominatorGrid l) :
    M *ᵥ x ∈ realDenominatorGrid (D * l) := by
  classical
  choose A hA using hM
  obtain ⟨z, hz⟩ := hx
  refine ⟨A *ᵥ z, funext fun i => ?_⟩
  change (((A *ᵥ z) i : ℤ) : ℝ) = ((D * l : ℕ) : ℝ) * (M *ᵥ x) i
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul,
    Nat.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : (z j : ℝ) = (l : ℝ) * x j := congrFun hz j
  rw [← hA i j, hj]
  ring

theorem real_matrix_complement_specified_denominator_grid
    (M : Matrix ι ι ℝ) (D l : ℕ)
    (hM : ∀ i j, ∃ z : ℤ, (D : ℝ) * M i j = z)
    (x : ι → ℝ) (hx : x ∈ realDenominatorGrid l) :
    x - M *ᵥ x ∈ realDenominatorGrid (D * l) := by
  obtain ⟨z, hz⟩ := hx
  obtain ⟨w, hw⟩ := real_matrix_specified_denominator_grid M D l hM x ⟨z, hz⟩
  refine ⟨fun i => (D : ℤ) * z i - w i, funext fun i => ?_⟩
  have hzi : (z i : ℝ) = (l : ℝ) * x i := congrFun hz i
  have hwi : (w i : ℝ) = ((D * l : ℕ) : ℝ) * (M *ᵥ x) i := congrFun hw i
  change (((D : ℤ) * z i - w i : ℤ) : ℝ) =
    ((D * l : ℕ) : ℝ) * (x i - (M *ᵥ x) i)
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, hzi, hwi]
  ring

theorem real_matrix_complement_linearMap_specified_denominator_grid
    (M : Matrix ι ι ℝ) (D l : ℕ)
    (hM : ∀ i j, ∃ z : ℤ, (D : ℝ) * M i j = z)
    (x : ι → ℝ) (hx : x ∈ realDenominatorGrid l) :
    ((LinearMap.id : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) - M.mulVecLin) x ∈ realDenominatorGrid (D * l) := by
  exact real_matrix_complement_specified_denominator_grid M D l hM x hx

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTagProjectionComplement
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {T : Type*} [Fintype T]

theorem rationalTagProjectionComplement_coordinate_bound
    (P : Matrix T T ℚ) {H : ℝ} (hH : 0 ≤ H)
    (hP : ∀ i j, |(P i j : ℝ)| ≤ H) (x : T → ℝ) (i : T) :
    |rationalTagProjectionComplement P x i| ≤
      (1 + (Fintype.card T : ℝ) * H) * ‖x‖ := by
  classical
  have hx (j : T) : |x j| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
  have hrow : |((fun i j => (P i j : ℝ)) *ᵥ x) i| ≤
      (Fintype.card T : ℝ) * H * ‖x‖ := by
    calc
      _ ≤ ∑ j, |(P i j : ℝ) * x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : T, H * ‖x‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hP i j) (hx j) (abs_nonneg _) hH
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  rw [rationalTagProjectionComplement_apply, Pi.sub_apply]
  calc
    _ ≤ |x i| + |((fun i j => (P i j : ℝ)) *ᵥ x) i| := abs_sub _ _
    _ ≤ ‖x‖ + (Fintype.card T : ℝ) * H * ‖x‖ := add_le_add (hx i) hrow
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffinePhysicalTerminalReset
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem affineResetNativeBudget_exp_bounds (C : ℕ) {pFull pMap q : ℝ}
    (hFull : 0 ≤ pFull) (hMap : 0 ≤ pMap) :
    let pNative := affineResetNativeBudget C pFull pMap q
    0 ≤ pNative ∧ pFull ≤ pNative ∧ pMap ≤ pNative ∧
      Real.exp ((pMap + 2) ^ 4) ≤ Real.exp pNative ∧
      Real.exp ((pFull + C) ^ C) ≤ Real.exp ((pNative + 2) ^ (1 : ℕ)) ∧
      Real.exp q ≤ Real.exp ((pNative + 2) ^ (1 : ℕ)) ∧
      Real.exp ((pMap + 2) ^ 3 + q) ≤ Real.exp ((pNative + 2) ^ (1 : ℕ)) := by
  obtain ⟨hp, hfull, hmap, hq, hslow, hmap4, hmapq⟩ :=
    affineResetNativeBudget_bounds C hFull hMap (q := q)
  refine ⟨hp, hfull, hmap, Real.exp_le_exp.mpr hmap4, ?_, ?_, ?_⟩ <;>
    apply Real.exp_le_exp.mpr <;> simp only [pow_one] <;> linarith

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineCanonicalBackendBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem allocatedAffineResetHeightLog_bounds {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ allocatedAffineResetHeightLog p ∧
      p ≤ allocatedAffineResetHeightLog p ∧
      (p + 4) ^ 11 ≤ allocatedAffineResetHeightLog p ∧
      (p + 3) ^ 7 ≤ allocatedAffineResetHeightLog p ∧
      (p + 2) ^ 4 ≤ allocatedAffineResetHeightLog p := by
  have hbase : 1 ≤ p + 4 := by linarith
  have hlinear : p + 4 ≤ (p + 4) ^ 12 := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (by norm_num : 1 ≤ 12)
  have h11 : (p + 4) ^ 11 ≤ (p + 4) ^ 12 :=
    pow_le_pow_right₀ hbase (by norm_num)
  have h7 : (p + 3) ^ 7 ≤ (p + 4) ^ 12 :=
    (pow_le_pow_left₀ (by linarith : 0 ≤ p + 3)
      (by linarith : p + 3 ≤ p + 4) 7).trans
      (pow_le_pow_right₀ hbase (by norm_num))
  have h4 : (p + 2) ^ 4 ≤ (p + 4) ^ 12 :=
    (pow_le_pow_left₀ (by linarith : 0 ≤ p + 2)
      (by linarith : p + 2 ≤ p + 4) 4).trans
      (pow_le_pow_right₀ hbase (by norm_num))
  dsimp only [allocatedAffineResetHeightLog]
  exact ⟨pow_nonneg (by linarith) _, (by linarith), h11, h7, h4⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open NilpotentLieFiltration

theorem power_le_recursiveParameter (C : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (p + C) ^ C ≤ finiteFreezingRecursiveParameter C p := by
  have hpow : 0 ≤ (p + C) ^ C := pow_nonneg (by positivity) _
  unfold finiteFreezingRecursiveParameter
  linarith only [hpow]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CandidatePhysicalOrdinaryBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem terminal_affine_budget_bounds {cumulative : ℝ} (hc : 0 ≤ cumulative) :
    0 ≤ certifiedAffineCenterBudget cumulative ∧
    ((cumulative + ((cumulative + 2) ^ 2 + 2) ^ 63) + 2) ^ 8 ≤
      certifiedAffineCenterBudget cumulative := by
  exact terminal_affine_budget_arithmetic hc (by positivity) (by positivity)

attribute [local irreducible] certifiedAffineCenterBudget

theorem terminal_mass_budget_bound (m nVars : ℕ) {p H : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hn : (nVars : ℝ) ≤ p) (hH : H ≤ p) :
    actualCandidateSlowProjectionMassBudget m nVars p H ≤ Real.exp (p ^ 2 + 4 * p + 3) := by
  have hpExp : p ≤ Real.exp p := by linarith only [Real.add_one_le_exp p]
  have hmExp : ((m + 1 : ℕ) : ℝ) ≤ Real.exp (p + 1) := by
    simp only [Nat.cast_add, Nat.cast_one]
    linarith only [hm, Real.add_one_le_exp (p + 1)]
  have hnExp : ((nVars + 1 : ℕ) : ℝ) ≤ Real.exp (p + 1) := by
    simp only [Nat.cast_add, Nat.cast_one]
    linarith only [hn, Real.add_one_le_exp (p + 1)]
  have hnPow : (((nVars + 1 : ℕ) : ℝ) ^ m) ≤ Real.exp ((m : ℝ) * (p + 1)) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (by positivity) hnExp m
  have hmain : p * Real.exp H *
      (((m + 1 : ℕ) : ℝ) * ((nVars + 1 : ℕ) : ℝ) ^ m) ≤
        Real.exp (p ^ 2 + 4 * p + 1) := by
    calc
      _ ≤ Real.exp p * Real.exp p *
          (Real.exp (p + 1) * Real.exp ((m : ℝ) * (p + 1))) :=
        mul_le_mul
          (mul_le_mul hpExp (Real.exp_le_exp.mpr hH) (Real.exp_nonneg _) (Real.exp_nonneg _))
          (mul_le_mul hmExp hnPow (by positivity) (Real.exp_nonneg _))
          (by positivity) (by positivity)
      _ = Real.exp (p + p + ((p + 1) + (m : ℝ) * (p + 1))) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hmul := mul_le_mul_of_nonneg_right hm (by linarith only [hp] : 0 ≤ p + 1)
        nlinarith only [hmul]
  have hQ : 0 ≤ p ^ 2 + 4 * p + 1 := by positivity
  have hone := Real.one_le_exp hQ
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by
    linarith only [Real.add_one_le_exp (2 : ℝ)]
  unfold actualCandidateSlowProjectionMassBudget
  calc
    _ ≤ 2 + Real.exp (p ^ 2 + 4 * p + 1) := add_le_add le_rfl hmain
    _ ≤ 3 * Real.exp (p ^ 2 + 4 * p + 1) := by linarith only [hone]
    _ ≤ Real.exp 2 * Real.exp (p ^ 2 + 4 * p + 1) :=
      mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem actualCandidateSlowProjectionMassBudget_terminal_bound
    (s m nTags nVars : ℕ) {p work H : ℝ}
    (hp : 0 ≤ p) (hs : (s : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (htags : (nTags : ℝ) ≤ p) (hvars : (nVars : ℝ) ≤ p)
    (hwork : work ≤ p) (hH : H ≤ p) :
    ((nTags : ℝ) + 1) ^ s * Real.exp work *
      (actualCandidateSlowProjectionMassBudget m nVars p H) ^ s ≤
        Real.exp ((p + 2) ^ 4) := by
  have htagsExp : (nTags : ℝ) + 1 ≤ Real.exp (p + 1) := by
    linarith only [htags, Real.add_one_le_exp (p + 1)]
  have htagsPow : ((nTags : ℝ) + 1) ^ s ≤ Real.exp ((s : ℝ) * (p + 1)) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (by positivity) htagsExp s
  have hmass := terminal_mass_budget_bound m nVars hp hm hvars hH
  have hmass0 : 0 ≤ actualCandidateSlowProjectionMassBudget m nVars p H :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (actualCandidateSlowProjectionMassBudget_one_le m nVars hp)
  have hmassPow : (actualCandidateSlowProjectionMassBudget m nVars p H) ^ s ≤
      Real.exp ((s : ℝ) * (p ^ 2 + 4 * p + 3)) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ hmass0 hmass s
  calc
    _ ≤ Real.exp ((s : ℝ) * (p + 1)) * Real.exp p *
        Real.exp ((s : ℝ) * (p ^ 2 + 4 * p + 3)) :=
      mul_le_mul
        (mul_le_mul htagsPow (Real.exp_le_exp.mpr hwork) (Real.exp_nonneg _) (Real.exp_nonneg _))
        hmassPow (pow_nonneg hmass0 _) (by positivity)
    _ = Real.exp ((s : ℝ) * (p + 1) + p + s * (p ^ 2 + 4 * p + 3)) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hs1 := mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ p + 1)
      have hs2 := mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ p ^ 2 + 4 * p + 3)
      have hpoly : p * (p + 1) + p + p * (p ^ 2 + 4 * p + 3) ≤ (p + 2) ^ 4 := by
        nlinarith only [hp, sq_nonneg p, pow_nonneg hp 3, pow_nonneg hp 4]
      linarith only [hs1, hs2, hpoly]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem candidatePhysicalOrdinaryBudget_observable {pFull pGeometry : ℝ}
    (hp : 0 ≤ pFull) (hgeometry : (pGeometry + 3) ^ 2 ≤ pFull) :
    RationalFilteredNilmanifold.nativeOptionTargetObservableBudget pGeometry ≤
      candidatePhysicalOrdinaryBudget pFull := by
  apply le_trans _ (candidatePhysicalOrdinaryBudget_bounds hp).2.2.2.1
  unfold RationalFilteredNilmanifold.nativeOptionTargetObservableBudget
  gcongr

theorem certifiedAffineCenterBudget_primitive_bounds {p : ℝ} (hp : 0 ≤ p) :
    p ≤ certifiedAffineCenterBudget p ∧ (p + 2) ^ 9 ≤ certifiedAffineCenterBudget p := by
  have hnonneg : 0 ≤ ((p + 2) ^ 2 + 2) ^ 63 := pow_nonneg (by positivity) _
  have hq : p ≤ p + ((p + 2) ^ 2 + 2) ^ 63 := le_add_of_nonneg_right hnonneg
  simpa only [certifiedAffineCenterBudget] using certifiedAffine_budget_lower_arithmetic hp hq

theorem candidatePhysicalOrdinaryBudget_mass {pFull pAffine mass : ℝ}
    (hp : 0 ≤ pFull) (ha : 0 ≤ pAffine)
    (hcenter : certifiedAffineCenterBudget pAffine ≤ pFull)
    (hmass : Real.exp (-pFull) ≤ mass) :
    Real.exp (-candidatePhysicalOrdinaryBudget pFull) ≤
      Real.exp (-((2 * certifiedAffineCenterBudget pAffine + 3) ^ 3)) * mass := by
  have hcenter0 : 0 ≤ certifiedAffineCenterBudget pAffine :=
    ha.trans (certifiedAffineCenterBudget_primitive_bounds ha).1
  have hloss : (2 * certifiedAffineCenterBudget pAffine + 3) ^ 3 + pFull ≤
      candidatePhysicalOrdinaryBudget pFull := by
    apply le_trans _ (candidatePhysicalOrdinaryBudget_bounds hp).2.2.1
    gcongr
  calc
    _ ≤ Real.exp (-((2 * certifiedAffineCenterBudget pAffine + 3) ^ 3)) *
        Real.exp (-pFull) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith only [hloss]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (Real.exp_nonneg _)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairUniformFactors
namespace OAI

universe u

section

namespace Erdos3.VectorPolynomial

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct Classical

def allocatedFrozenTaggedPairBudget (s C A : ℕ) (pGeo p : ℝ) : ℝ :=
  (fixedAdaptedSymbolTransferInput pGeo
    (pGeo + p + ((p + 2 + C) ^ C + (s : ℝ) * (9 * p + 23))) + A) ^ A

end Erdos3.VectorPolynomial

end

end OAI
end


