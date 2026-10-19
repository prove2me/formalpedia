-- Prove2me | Definitions.Def_OAIE3v2B138
-- name    : OAIE3v2B138
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:14:24.993423+00:00
-- url     : https://prove2.me/theorems/545c6569-e54f-4c35-a600-8ed63522527f
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 140 of 311
-- statement:
--   Definitions bundle 140 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B114`, `OAIE3v2B115`, `OAIE3v2B116`, `OAIE3v2B118`, `OAIE3v2B119`, `OAIE3v2B122`, `OAIE3v2B123`, `OAIE3v2B124`, `OAIE3v2B125` of this split.
--
--   Modules: `Dynamics/FilteredSectionSingleDenominatorBudget.lean`, `Estimates/AllocatedFiberCap.lean`, `Estimates/AllocatedPhysicalLongIdealCap.lean`, `Estimates/CenteredFiniteSliceResidualEnvelope.lean`, `Estimates/CoefficientSliceEmbedding.lean`, `Estimates/DenseCommonStrideCardRatio.lean`, `Estimates/MarginalTailModeling.lean`, `Estimates/NativeEqualDimension.lean`, `Estimates/RelativePatchAmplification.lean`, `Estimates/SiteTwistCommonModulus.lean`, `Estimates/UniformControlledNativeExternalNetsOfRecovery.lean`, `Lattices/AffineOneSiteNormalizedLaw.lean`, `Lattices/LieSubalgebraLatticeInnerGrid.lean`, `Lattices/SourceLatticeCover.lean`, `Linear/NativeChartKernel.lean`, `Linear/NativeMarkedKernelRepresentatives.lean`, `Linear/ProductANOVAEnergyOrder.lean`, `Linear/RelativePatchRankTightening.lean`, `Nilpotent/BoxNiltestDetection.lean`, `Nilpotent/IdealInvariantNiltestBudget.lean`, `Nilpotent/NiltestAffineProjection.lean`, `Nilpotent/NiltestBasepointNormalization.lean`, `Nilpotent/PolynomialShearNilmanifold.lean`, `Nilpotent/SumNilmanifoldFactors.lean`, `Nilpotent/UnitComparisonNiltest.lean`, `Polynomial/PolynomialShearParameterBudget.lean`, `Probability/AllocatedAmbientDensity.lean`, `Probability/AllocatedFixedPositiveDensity.lean`, `Probability/ContainedProgressionCubeLaw.lean`, `Probability/JointProductiveMeasure.lean`, `Probability/RelativeSliceFiniteLaw.lean`, `Sampling/FixedPathSlicedGridMeshBudget.lean`, `Sampling/NativeGridRightDictionary.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B114
import Definitions.Def_OAIE3v2B115
import Definitions.Def_OAIE3v2B116
import Definitions.Def_OAIE3v2B118
import Definitions.Def_OAIE3v2B119
import Definitions.Def_OAIE3v2B122
import Definitions.Def_OAIE3v2B123
import Definitions.Def_OAIE3v2B124
import Definitions.Def_OAIE3v2B125

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestBasepointNormalization
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def normalizeBasepoint (T : D.Niltest w) (a γ : D.RealGroup) (A : ℝ≥0)
    (hA : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => a • x)) : D.Niltest w where
  orbit := D.filtration.realification.normalizePolynomialOrbit w T.orbit a γ
  observable := fun x => T.observable (a • x)
  normBound := T.normBound
  lipBound := T.lipBound * A
  norm_le x := T.norm_le (a • x)
  lipschitz := by
    let := D.metricSpace
    exact T.lipschitz.comp hA

theorem normalizeBasepoint_zero (T : D.Niltest w) (a γ : D.RealGroup) (A : ℝ≥0)
    (hA : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => a • x))
    (hg : D.filtration.realification.polynomialOrbitEval w 0 T.orbit = a * γ) :
    D.filtration.realification.polynomialOrbitEval w 0 (T.normalizeBasepoint a γ A hA).orbit = 1 :=
  D.filtration.realification.normalizePolynomialOrbit_zero w T.orbit a γ hg

theorem normalizeBasepoint_eval (T : D.Niltest w) (a γ : D.RealGroup) (A : ℝ≥0)
    (hA : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => a • x))
    (hγ : γ ∈ D.realLattice) (x : σ → ℤ) :
    (T.normalizeBasepoint a γ A hA).eval x = T.eval x := by
  change T.observable (a • QuotientGroup.mk
    (D.filtration.realification.polynomialOrbitEval w x
      (D.filtration.realification.normalizePolynomialOrbit w T.orbit a γ))) = _
  rw [NilpotentLieFiltration.normalizePolynomialOrbit_eval]
  simp only [MulAction.Quotient.smul_mk, smul_eq_mul, ← mul_assoc, mul_inv_cancel, one_mul]
  exact congrArg T.observable (QuotientGroup.mk_mul_of_mem _ (D.realLattice.inv_mem hγ))

theorem normalizeBasepoint_complexity (T : D.Niltest w) (a γ : D.RealGroup) (A : ℝ≥0)
    (hA : letI := D.metricSpace; LipschitzWith A (fun x : D.Space => a • x))
    {p q : ℝ} (hT : T.ComplexityLE p) (hq : 0 ≤ q) (hbound : (A : ℝ) ≤ Real.exp q) :
    (T.normalizeBasepoint a γ A hA).ComplexityLE (p + q) := by
  refine ⟨hT.1.mono D (le_add_of_nonneg_right hq), ?_⟩
  change Real.log (2 + (T.normBound : ℝ) + (T.lipBound : ℝ) * A) ≤ p + q
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  have h1 : 1 ≤ Real.exp q := Real.one_le_exp hq
  calc
    _ ≤ (2 + (T.normBound : ℝ)) * Real.exp q + (T.lipBound : ℝ) * Real.exp q :=
      add_le_add (le_mul_of_one_le_right (by positivity) h1)
        (mul_le_mul_of_nonneg_left hbound T.lipBound.coe_nonneg)
    _ = (2 + (T.normBound : ℝ) + (T.lipBound : ℝ)) * Real.exp q := by ring
    _ ≤ Real.exp p * Real.exp q := mul_le_mul_of_nonneg_right (observable_budget hT) (Real.exp_nonneg _)
    _ = _ := (Real.exp_add _ _).symm

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FilteredSectionSingleDenominatorBudget
namespace OAI

section

namespace Erdos3

theorem filtered_section_single_denominator_le_exp {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (D : Matrix κ ι ℚ) (S : Matrix ι κ ℚ) (l : ℕ) {H : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p)
    (hD : ∀ i j, RationalHeightLE (D i j) H)
    (hS : ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card κ) H))
    (hl : (l : ℝ) ≤ Real.exp p) :
    ((matrixDenominator S * l : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 11) := by
  have hqD : 1 ≤ matrixDenominator D := matrixDenominator_pos D
  have hnat := Nat.mul_le_mul_right l (Nat.mul_le_mul_left (matrixDenominator S) hqD)
  simp only [Nat.mul_one] at hnat
  exact (Nat.cast_le.mpr hnat).trans
    (filtered_section_pair_denominator_le_exp D S l hp hι hκ hH hD hS hl)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PolynomialShearNilmanifold
namespace OAI

section

namespace Erdos3

open Module

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) [Fintype (PolynomialShearIndex w)]

theorem polynomialShearLayerBasis_height (r : ℕ)
    (i : {j : Fin (Fintype.card (PolynomialShearIndex w)) // r ≤ polynomialShearOrderedWeight w j}) (j) :
    RationalHeightLE ((polynomialShearOrderedBasis w).repr
      (polynomialShearLayerBasis w r i).val j) 1 := by
  rw [polynomialShearLayerBasis, supportedSubmoduleBasis_coe]
  exact basis_repr_height_one (polynomialShearOrderedBasis w) _ _

theorem polynomialShearLayerFinBasis_height (r : ℕ) (i j) :
    RationalHeightLE ((polynomialShearOrderedBasis w).repr
      (polynomialShearLayerFinBasis w r i).val j) 1 := by
  rw [polynomialShearLayerFinBasis, Basis.reindex_apply]
  exact polynomialShearLayerBasis_height w r _ _

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

theorem shearKernelLipBound_le_exp {σ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)
    (M : ℝ≥0) {u : ℝ} (hu : 0 ≤ u) (hA : (A.kernel.lip : ℝ) ≤ Real.exp u) :
    (A.shearKernelLipBound M : ℝ) ≤ Real.exp (shearKernelLogBudget s d M u) := by
  have hM : 1 + (M : ℝ) ≤ Real.exp (M : ℝ) := by linarith [Real.add_one_le_exp (M : ℝ)]
  have hd : (d : ℝ) ≤ Real.exp (d : ℝ) := by linarith [Real.add_one_le_exp (d : ℝ)]
  have hs : (s : ℝ) ≤ Real.exp (s : ℝ) := by linarith [Real.add_one_le_exp (s : ℝ)]
  have hR : (((1 + M) ^ (s * d) + 1 : ℝ≥0) : ℝ) ≤
      Real.exp ((s * d : ℕ) * (M : ℝ) + 1) := by
    have h := add_le_exp_add_one (by positivity : 0 ≤ (s * d : ℕ) * (M : ℝ))
      (le_refl (0 : ℝ)) (shearRadius_le_exp s d M) (by simp : (1 : ℝ) ≤ Real.exp 0)
    simpa only [NNReal.coe_add, NNReal.coe_one, add_zero] using h
  change max (1 : ℝ) ((A.kernel.lip : ℝ) *
    ((1 + M) * d * s * ((((1 + M) ^ (s * d) + 1 : ℝ≥0) : ℝ) ^ (s * (d + 1))))) ≤ _
  apply max_le (Real.one_le_exp (shearKernelLogBudget_nonneg s d M.coe_nonneg hu))
  calc
    _ ≤ Real.exp u * (Real.exp (M : ℝ) * Real.exp (d : ℝ) * Real.exp (s : ℝ) *
        (Real.exp ((s * d : ℕ) * (M : ℝ) + 1)) ^ (s * (d + 1))) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1
      unfold shearKernelLogBudget
      ring

theorem shearObservable_log_bound {σ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)
    [Fintype (PolynomialShearIndex A.weight)] (M : ℝ≥0) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hA : (A.kernel.lip : ℝ) ≤ Real.exp u)
    (hC : (bchLogMetricConstant s (Fintype.card (PolynomialShearIndex A.weight)) (2 * s + 1) 1 : ℝ) ≤ Real.exp v) :
    Real.log (3 + (A.shearObservableLipBound M : ℝ)) ≤
      shearKernelLogBudget s d M u + shearActionLogBudget s d M + v + 3 := by
  let E := shearKernelLogBudget s d M u + shearActionLogBudget s d M + v
  have hk := shearKernelLipBound_le_exp A M hu hA
  have ht := shearDisplacementBound_le_exp s d M
  have hE : 0 ≤ E := add_nonneg
    (add_nonneg (shearKernelLogBudget_nonneg s d M.coe_nonneg hu)
      (shearActionLogBudget_nonneg s d M.coe_nonneg)) hv
  have hL : (A.shearObservableLipBound M : ℝ) ≤ Real.exp E := by
    change max _ _ ≤ _
    apply max_le
    · apply hC.trans (Real.exp_le_exp.mpr ?_)
      dsimp [E]
      linarith [shearKernelLogBudget_nonneg s d M.coe_nonneg hu, shearActionLogBudget_nonneg s d M.coe_nonneg]
    · calc
        _ ≤ Real.exp (shearKernelLogBudget s d M u) * Real.exp (shearActionLogBudget s d M) * Real.exp v := by
          exact mul_le_mul (mul_le_mul hk ht (NNReal.coe_nonneg _) (Real.exp_nonneg _))
            hC (NNReal.coe_nonneg _) (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  have hfour : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  calc
    _ ≤ 4 * Real.exp E := by linarith [Real.one_le_exp hE]
    _ ≤ Real.exp 3 * Real.exp E := mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [E]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchAmplification
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem relativePatchComplexity_rank_le {X : Type*} {s d : ℕ}
    (A : PolynomialPatch X s d) : (d : ℝ) ≤ relativePatchComplexity A := by
  have hlog : 0 ≤ Real.log (1 + (A.kernel.lip : ℝ)) :=
    Real.log_nonneg (by linarith [A.kernel.lip.coe_nonneg])
  exact le_add_of_nonneg_right hlog

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedPathSlicedGridMeshBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def fixedPathSlicedGridMeshFloor (D C V cost E : ℝ) : ℕ :=
  ⌈Real.exp (fixedPathSlicedGridMeshLog D C V cost E)⌉₊

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding
namespace OAI

section

namespace Erdos3.ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

noncomputable def integerOffset (k : Option I → Fin d.cellCount) : Option I → ℝ :=
  fun i => (d.residue i).val + (d.modulus i : ℝ) * ((d.cellLength : ℝ) * (k i).val - d.length)

end Erdos3.ScalarCubeLocalizationData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedAmbientDensity
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedCoefficientAmbientDensity_eq (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (x : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    allocatedCoefficientAmbientDensity B U b o S (coefficientAmbientTorus U x) =
      allocatedCoefficientDensity B U b hb o hR hσ S x := by
  exact coefficientAmbientDensity_eq U b hb o _ _ _ _
    (fun j i d => (allocatedLayerIntegerInterpolation_spec B U b S hR hσ j i d).1)
    (allocatedLayerColumns_quarter_support B U b hR hσ S o hσ1 C hC hchart hsmall) x

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFiberCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem coefficientProductDensity_fiberAverage_cap {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [∀ j, MeasurableSpace (SubspaceArrayTorus Unit (U j))]
    [∀ j, BorelSpace (SubspaceArrayTorus Unit (U j))]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ s : CoefficientSlot K m, Measure (SubspaceArrayTorus Unit (U s.1)))
    [∀ s, (ν s).IsAddLeftInvariant] [∀ s, IsProbabilityMeasure (ν s)]
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    (hf : ∀ s, Measurable (f s)) (hfi : ∀ s, Integrable (f s) (ν s))
    (hf0 : ∀ s x, 0 ≤ f s x) (hmass : ∀ s, (∫ x, f s x ∂ν s) = 1)
    (C : Fin m → ℝ)
    (hC : ∀ (s : CoefficientSlot K m), s.2.val = 0 → ∀ x, f s x ≤ C s.1)
    (t : K → ℤ) (y : CoefficientTorus (K := Empty) U) :
    Integrable (fun x => coefficientProductDensity U f (coefficientFiberMap U t y x)) μ ∧
      coefficientFiberAverage U μ t (coefficientProductDensity U f) y ∈ Set.Icc (0 : ℝ) (∏ j, C j) := by
  have hR := nonconstantCoefficientDensity_probability U μ ν f hfi hf0 hmass
  have hD : Measurable (coefficientProductDensity U f) :=
    Finset.measurable_prod _ (fun s _ => (hf s).comp
      ((measurable_pi_apply s).comp (coefficientCoordinateTorus_continuous U).measurable))
  have hb := coefficientProductDensity_fiber_bound U f hf0 C hC t y
  have hi : Integrable (fun x => coefficientProductDensity U f (coefficientFiberMap U t y x)) μ :=
    (hR.1.const_mul (∏ j, C j)).mono'
      (hD.comp (coefficientFiberMap_continuous U t y).measurable).aestronglyMeasurable
      (ae_of_all μ (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (coefficientProductDensity_nonneg U f hf0 _)]
        exact hb x))
  refine ⟨hi, coefficientFiberAverage_nonneg U μ t _ (coefficientProductDensity_nonneg U f hf0) y, ?_⟩
  calc
    _ ≤ ∫ x, (∏ j, C j) * coefficientProductDensity U (nonconstantCoefficientFactor U f) x ∂μ :=
      integral_mono hi (hR.1.const_mul _) hb
    _ = ∏ j, C j := by rw [integral_const_mul, hR.2.2, mul_one]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)

variable [∀ j, MeasurableSpace (SubspaceArrayTorus Unit (U j))]
variable [∀ j, BorelSpace (SubspaceArrayTorus Unit (U j))]

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include ν in
theorem canonicalCoefficientDensity_fiber_cap (hw : ∀ j i d, 0 < w j i d)
    (hs : ∀ j d x, mixedCoefficientDensity (fun i => c j i d) (fun i => w j i d)
      (fun i => p j i d) x ≠ 0 → normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) x) ∈ standardLatticeSmallBox (J j))
    (C : Fin m → ℝ)
    (hC : ∀ (s : CoefficientSlot K m), s.2.val = 0 → ∀ y,
      canonicalCoefficientFactor U b hb o c w p s y ≤ C s.1)
    (t : K → ℤ) (y : CoefficientTorus (K := Empty) U) :
    Integrable (fun x => canonicalCoefficientDensity U b hb o c w p (coefficientFiberMap U t y x)) μ ∧
      coefficientFiberAverage U μ t (canonicalCoefficientDensity U b hb o c w p) y ∈
        Set.Icc (0 : ℝ) (∏ j, C j) := by
  let ξ := fun s : CoefficientSlot K m => euclideanSubspaceTorusMeasure (U s.1) (ν s.1)
  let : ∀ s, IsProbabilityMeasure (ξ s) :=
    fun s => euclideanSubspaceTorusMeasure_probability (U s.1) (ν s.1)
  let : ∀ s, (ξ s).IsAddLeftInvariant :=
    fun s => euclideanSubspaceTorusMeasure_invariant (U s.1) (ν s.1)
  have hmass (s : CoefficientSlot K m) := canonicalMixedDensity_mass _ (b s.1) (hb s.1) (o s.1)
    (ν s.1) (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => hw s.1 i s.2)
    (fun i => p s.1 i s.2) (hs s.1 s.2)
  have hfactor (s : CoefficientSlot K m) := euclideanSubspaceTorusMeasure_mass (U s.1) (ν s.1)
    _ (hmass s).1 (hmass s).2
  rw [canonicalCoefficientDensity_product]
  exact coefficientProductDensity_fiberAverage_cap U μ ξ (canonicalCoefficientFactor U b hb o c w p)
    (canonicalCoefficientFactor_measurable U b hb o c w p) (fun s => (hfactor s).1)
    (fun s x => canonicalMixedDensity_nonneg _ (b s.1) (hb s.1) (o s.1) _ _
      (fun i => hw s.1 i s.2) _ _) (fun s => (hfactor s).2) C hC t y

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineOneSiteNormalizedLaw
namespace OAI

section

namespace Erdos3

theorem selectedResidueSmoothPMF_test_le_of_complex {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D g φ : (K × I → ℤ) → ℝ) {C ε : ℝ}
    (hg : ∀ x, g x ≤ C) (hφ : ∀ x, 0 ≤ φ x)
    (he : ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) *
        ((φ x : ℂ) * (D x : ℂ))) -
      ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) *
        ((φ x : ℂ) * (g x : ℂ))‖ ≤ ε) :
    (∑' x, (selectedResidueSmoothPMF modulus G V hV hZ x).toReal * (φ x * D x)) ≤
      C * (∑' x, (selectedResidueSmoothPMF modulus G V hV hZ x).toReal * φ x) + ε := by
  let prob := selectedResidueFiniteLaw modulus G V hV hZ
  have hmean (f : (K × I → ℤ) → ℝ) : prob.mean (fun x => f x.val) =
      ∑' x, (selectedResidueSmoothPMF modulus G V hV hZ x).toReal * f x :=
    selectedResidueFiniteLaw_mean modulus G V hV hZ f
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_tsum, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at he
  have h := prob.mean_mul_le_of_capped_comparison (ε := ε) (fun x => D x.val)
    (fun x => g x.val) (fun x => φ x.val) (fun x => hφ x.val) (fun x => hg x.val) (by
      rw [hmean (fun x => D x * φ x), hmean (fun x => g x * φ x)]
      simpa only [mul_comm, mul_left_comm, mul_assoc] using he)
  rw [hmean (fun x => D x * φ x), hmean φ] at h
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarginalTailModeling
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

noncomputable def weightedEuclideanMap (p : FiniteProbabilityWeights Ω) :
    (Ω → ℂ) →ₗ[ℝ] EuclideanSpace ℂ Ω :=
  (WithLp.linearEquiv 2 ℝ (Ω → ℂ)).symm.toLinearMap.comp
    (LinearMap.pi fun x => Real.sqrt (p.weight x) • LinearMap.proj x)

theorem weightedEuclideanMap_norm_sq (p : FiniteProbabilityWeights Ω) (v : Ω → ℂ) :
    ‖weightedEuclideanMap p v‖ ^ 2 = p.mean (fun x => ‖v x‖ ^ 2) := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro x _
  change ‖Real.sqrt (p.weight x) • v x‖ ^ 2 = p.weight x * ‖v x‖ ^ 2
  rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (p.nonneg x)]

theorem exists_weighted_convex_approximation (p : FiniteProbabilityWeights Ω)
    {S : Set (Ω → ℂ)} {z : Ω → ℂ} (hz : z ∈ convexHull ℝ S)
    (hS : ∀ q ∈ S, ∀ x, ‖q x‖ ≤ 1) (n : ℕ) (hn : 0 < n) :
    ∃ q : Fin n → (Ω → ℂ), (∀ i, q i ∈ S) ∧
      p.mean (fun x => ‖((n : ℝ)⁻¹ • (∑ i, q i) - z) x‖ ^ 2) ≤ 1 / (n : ℝ) := by
  classical
  let e := weightedEuclideanMap p
  have hz' : e z ∈ convexHull ℝ (e '' S) := by
    rw [← e.image_convexHull S]
    exact ⟨z, hz, rfl⟩
  have hS' : ∀ v ∈ e '' S, ‖v‖ ≤ 1 := by
    rintro v ⟨q, hq, rfl⟩
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
    change ‖weightedEuclideanMap p q‖ ^ 2 ≤ 1 ^ 2
    rw [weightedEuclideanMap_norm_sq, one_pow]
    exact (p.mean_mono (fun x => by
      nlinarith [hS q hq x, norm_nonneg (q x)])).trans_eq (p.mean_const 1)
  obtain ⟨v, hv, hsq⟩ := exists_convex_empirical_average hz' hS' n hn
  have hpre : ∀ i, ∃ q ∈ S, e q = v i := hv
  choose q hq heq using hpre
  have hid : e ((n : ℝ)⁻¹ • (∑ i, q i) - z) =
      (n : ℝ)⁻¹ • (∑ i, v i) - e z := by
    simp only [map_sub, map_smul, map_sum, heq]
  rw [← hid, one_pow] at hsq
  exact ⟨q, hq, (weightedEuclideanMap_norm_sq p _).ge.trans hsq⟩

theorem seminorm_sq_le_weighted_square_mean (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) {K : ℝ}
    (hX : ∀ v, X v ≤ K * p.mean (fun x => ‖v x‖)) (v : Ω → ℂ) :
    (X v) ^ 2 ≤ K ^ 2 * p.mean (fun x => ‖v x‖ ^ 2) := by
  have h := pow_le_pow_left₀ (apply_nonneg X v) (hX v) 2
  rw [mul_pow] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (p.mean_square_le (fun x => ‖v x‖)) (sq_nonneg K))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem mem_closure_model_of_weighted_detector (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) {S : Set (Ω → ℂ)} (hS : Balanced ℂ S) (hSn : S.Nonempty)
    {K M beta tau : ℝ} (hK : 0 ≤ K) (hM : 0 < M) (hbeta : 0 < beta) (htau : 0 < tau)
    (hX : ∀ v, X v ≤ K * p.mean (fun x => ‖v x‖))
    (hdetect : ∀ psi : Ω → ℂ, (∀ x, ‖psi x‖ ≤ K / tau) → tau / M ^ 2 ≤ X psi →
      ∃ Q ∈ S, beta ≤ ‖p.correlation psi Q‖)
    (b : Ω → ℂ) (hb : ∀ x, ‖b x‖ ≤ M) :
    b ∈ closure ((2 / beta : ℝ) • convexHull ℝ S + X.closedBall 0 tau) := by
  apply mem_closure_model_set_of_dual_detector X hS hSn (by positivity) htau b
  intro f hfb hdual
  have hzero := modeling_dual_zero_weight p X f.toLinearMap htau hX hdual
  have hcap := weightedDualVector_cap p X f.toLinearMap hK htau hX hdual
  have hlarge := weightedDualVector_detectable p X f.toLinearMap b hM htau hb hfb hdual hzero
  obtain ⟨Q, hQ, hcor⟩ := hdetect (weightedDualVector p f.toLinearMap) hcap hlarge.le
  rw [p.norm_correlation_symm, ← functional_eq_weighted_inner p f.toLinearMap hzero] at hcor
  refine ⟨Q, hQ, ?_⟩
  have h := mul_le_mul_of_nonneg_left hcor (show 0 ≤ 2 / beta by positivity)
  rw [div_mul_cancel₀ 2 hbeta.ne'] at h
  exact (by norm_num : (1 : ℝ) ≤ 2).trans h

theorem exists_convex_model_of_weighted_detector (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) {S : Set (Ω → ℂ)} (hS : Balanced ℂ S) (hSn : S.Nonempty)
    {K M beta tau eta : ℝ} (hK : 0 ≤ K) (hM : 0 < M) (hbeta : 0 < beta)
    (htau : 0 < tau) (heta : 0 < eta)
    (hX : ∀ v, X v ≤ K * p.mean (fun x => ‖v x‖))
    (hdetect : ∀ psi : Ω → ℂ, (∀ x, ‖psi x‖ ≤ K / tau) → tau / M ^ 2 ≤ X psi →
      ∃ Q ∈ S, beta ≤ ‖p.correlation psi Q‖)
    (b : Ω → ℂ) (hb : ∀ x, ‖b x‖ ≤ M) :
    ∃ z ∈ convexHull ℝ S, X (b - (2 / beta : ℝ) • z) ≤ tau + eta := by
  have hc := mem_closure_model_of_weighted_detector p X hS hSn hK hM hbeta htau hX hdetect b hb
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp hc (eta / (K + 1)) (by positivity)
  obtain ⟨v, hv, e, he, hve⟩ := Set.mem_add.mp hy
  obtain ⟨z, hz, hzv⟩ := Set.mem_smul_set.mp hv
  have hxe : X e ≤ tau := X.mem_closedBall_zero.mp he
  have hnorm : ‖b - y‖ < eta / (K + 1) := by
    simpa only [dist_eq_norm] using hdist
  have hsmall : K * ‖b - y‖ ≤ eta := by
    have h := (lt_div_iff₀ (show 0 < K + 1 by linarith)).mp hnorm
    nlinarith [norm_nonneg (b - y)]
  have hmean : p.mean (fun x => ‖(b - y) x‖) ≤ ‖b - y‖ :=
    (p.mean_mono (fun x => norm_le_pi_norm (b - y) x)).trans_eq (p.mean_const ‖b - y‖)
  have hxy : X (b - y) ≤ eta := (hX (b - y)).trans
    ((mul_le_mul_of_nonneg_left hmean hK).trans hsmall)
  refine ⟨z, hz, ?_⟩
  have hid : b - (2 / beta : ℝ) • z = (b - y) + e := by
    rw [← hve, ← hzv]
    abel
  rw [hid]
  exact (map_add_le_add X _ _).trans (by linarith)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem scaled_weighted_empirical_seminorm_bound (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) {K R : ℝ} (hR : 0 ≤ R)
    (hX : ∀ v, X v ≤ K * p.mean (fun x => ‖v x‖))
    (v : Ω → ℂ) (n : ℕ) (hn : 0 < n)
    (hv : p.mean (fun x => ‖v x‖ ^ 2) ≤ 1 / (n : ℝ)) :
    X (R • v) ≤ Real.sqrt (R ^ 2 * K ^ 2 / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq := (seminorm_sq_le_weighted_square_mean p X hX v).trans
    (mul_le_mul_of_nonneg_left hv (sq_nonneg K))
  have hsmul : X (R • v) = R * X v := by
    change (X.restrictScalars ℝ) (R • v) = _
    rw [map_smul_eq_mul, Real.norm_of_nonneg hR]
    rfl
  have hscaled : (X (R • v)) ^ 2 ≤ R ^ 2 * K ^ 2 / n := by
    rw [hsmul, mul_pow]
    have h := mul_le_mul_of_nonneg_left hsq (sq_nonneg R)
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_assoc] using h
  have hroot := Real.sq_sqrt (show 0 ≤ R ^ 2 * K ^ 2 / n by positivity)
  exact (sq_le_sq₀ (apply_nonneg X _) (Real.sqrt_nonneg _)).mp (hscaled.trans_eq hroot.symm)

variable [DecidableEq Ω]

theorem exists_weighted_model_of_detector (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) {S : Set (Ω → ℂ)}
    (hS : Balanced ℂ S) (hSn : S.Nonempty) (hSbound : ∀ Q ∈ S, ∀ x, ‖Q x‖ ≤ 1)
    {K M beta tau : ℝ} (hK : 0 ≤ K) (hM : 0 < M) (hbeta : 0 < beta) (htau : 0 < tau)
    (hX : ∀ v, X v ≤ K * p.mean (fun x => ‖v x‖))
    (hdetect : ∀ psi : Ω → ℂ, (∀ x, ‖psi x‖ ≤ K / tau) → tau / M ^ 2 ≤ X psi →
      ∃ Q ∈ S, beta ≤ ‖p.correlation psi Q‖)
    (b : Ω → ℂ) (hb : ∀ x, ‖b x‖ ≤ M) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (Ω → ℂ)) (c : Fin n → ℝ) (e : Ω → ℂ),
      (∀ i, Q i ∈ S) ∧ b = (∑ i, c i • Q i) + e ∧
      (∑ i, |c i|) ≤ 2 / beta ∧ X e ≤ 2 * tau ∧
      (n : ℝ) ≤ 1 + 4 * K ^ 2 / (beta ^ 2 * tau ^ 2) := by
  let R := 2 / beta
  have hR : 0 < R := by dsimp only [R]; positivity
  obtain ⟨n, hn, hlen, hsmall⟩ := exists_empirical_length (R := R) (K := K) htau
  let s := Real.sqrt (R ^ 2 * K ^ 2 / n)
  have hs : s < tau := hsmall
  let eta := (tau - s) / 2
  have heta : 0 < eta := by dsimp only [eta]; linarith
  obtain ⟨z, hz, hmodel⟩ := exists_convex_model_of_weighted_detector p X hS hSn
    hK hM hbeta htau heta hX hdetect b hb
  obtain ⟨Q, hQ, happrox⟩ := exists_weighted_convex_approximation p hz hSbound n hn
  let avg := (n : ℝ)⁻¹ • (∑ i, Q i)
  have hnoise : X (R • (avg - z)) ≤ s :=
    scaled_weighted_empirical_seminorm_bound p X hR.le hX (avg - z) n hn happrox
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let c : Fin n → ℝ := fun _ => R / n
  have hstruct : (∑ i, c i • Q i) = R • avg := by
    calc
      _ = (R / (n : ℝ)) • (∑ i, Q i) := by rw [Finset.smul_sum]
      _ = _ := by dsimp only [avg]; rw [smul_smul]; congr 1
  have hcost : (∑ i, |c i|) = R := by
    simp only [c, abs_of_nonneg (div_nonneg hR.le hnR.le), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  refine ⟨n, hn, Q, c, b - ∑ i, c i • Q i, hQ, ?_, hcost.le, ?_, ?_⟩
  · abel
  · rw [hstruct]
    have hid : b - R • avg = (b - R • z) - R • (avg - z) := by
      rw [smul_sub]
      abel
    rw [hid]
    have h := map_sub_le_add X (b - R • z) (R • (avg - z))
    change X (b - R • z) ≤ tau + eta at hmodel
    dsimp only [eta] at hmodel
    linarith
  · have heq : R ^ 2 * K ^ 2 / tau ^ 2 = 4 * K ^ 2 / (beta ^ 2 * tau ^ 2) := by
      dsimp only [R]
      field_simp
      ring
    simpa only [heq] using hlen

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem seminorm_mask_le (p : FiniteProbabilityWeights Ω) (G : Finset Ω)
    (X : Seminorm ℂ (Ω → ℂ)) (m : Ω → ℝ) {C C₀ : ℝ}
    (hC : 0 ≤ C) (_hC₀ : 0 ≤ C₀)
    (hX : ∀ v, X v ≤ C * p.mean (fun x => m x * ‖v x‖))
    (hgood : ∀ x ∈ G, m x ≤ C₀) (v : Ω → ℂ) :
    X (finiteMask G v) ≤ C * C₀ * p.mean (fun x => if x ∈ G then ‖v x‖ else 0) := by
  have hmean : p.mean (fun x => m x * ‖finiteMask G v x‖) ≤
      C₀ * p.mean (fun x => if x ∈ G then ‖v x‖ else 0) := by
    rw [← p.mean_const_mul]
    apply p.mean_mono
    intro x
    by_cases hx : x ∈ G
    · simpa only [finiteMask_apply, hx, ite_true] using
        mul_le_mul_of_nonneg_right (hgood x hx) (norm_nonneg (v x))
    · simp [hx]
  exact (hX _).trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hmean hC)

theorem seminorm_mask_le_condition (p : FiniteProbabilityWeights Ω) (G : Finset Ω)
    (hG : 0 < p.mass G) (X : Seminorm ℂ (Ω → ℂ)) (m : Ω → ℝ) {C C₀ : ℝ}
    (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hX : ∀ v, X v ≤ C * p.mean (fun x => m x * ‖v x‖))
    (hgood : ∀ x ∈ G, m x ≤ C₀) (v : Ω → ℂ) :
    X (finiteMask G v) ≤ C * C₀ * (p.condition G hG).mean (fun x => ‖v x‖) := by
  have h := seminorm_mask_le p G X m hC hC₀ hX hgood v
  rw [← p.mass_mul_condition_mean G hG] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hC₀)
  exact mul_le_of_le_one_left ((p.condition G hG).mean_nonneg (fun x => norm_nonneg _))
    (p.mass_le_one G)

theorem seminorm_tail_le (p : FiniteProbabilityWeights Ω) (G : Finset Ω)
    (X : Seminorm ℂ (Ω → ℂ)) (m : Ω → ℝ) {C B : ℝ}
    (hC : 0 ≤ C) (hm : ∀ x, 0 ≤ m x)
    (hX : ∀ v, X v ≤ C * p.mean (fun x => m x * ‖v x‖))
    (v : Ω → ℂ) (hv : ∀ x, ‖v x‖ ≤ B) :
    X (v - finiteMask G v) ≤ C * B * p.mean (fun x => if x ∈ G then 0 else m x) := by
  have hmean : p.mean (fun x => m x * ‖(v - finiteMask G v) x‖) ≤
      B * p.mean (fun x => if x ∈ G then 0 else m x) := by
    rw [← p.mean_const_mul]
    apply p.mean_mono
    intro x
    by_cases hx : x ∈ G
    · simp [hx]
    · simpa only [Pi.sub_apply, finiteMask_apply, hx, ite_false, sub_zero, mul_comm B]
        using mul_le_mul_of_nonneg_left (hv x) (hm x)
  exact (hX _).trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hmean hC)

theorem seminorm_le_mask_add_tail (p : FiniteProbabilityWeights Ω) (G : Finset Ω)
    (X : Seminorm ℂ (Ω → ℂ)) (m : Ω → ℝ) {C B : ℝ}
    (hC : 0 ≤ C) (hm : ∀ x, 0 ≤ m x)
    (hX : ∀ v, X v ≤ C * p.mean (fun x => m x * ‖v x‖))
    (v : Ω → ℂ) (hv : ∀ x, ‖v x‖ ≤ B) :
    X v ≤ X (finiteMask G v) +
      C * B * p.mean (fun x => if x ∈ G then 0 else m x) := by
  calc
    X v = X (finiteMask G v + (v - finiteMask G v)) := by congr 1; abel
    _ ≤ X (finiteMask G v) + X (v - finiteMask G v) := map_add_le_add X _ _
    _ ≤ _ := add_le_add le_rfl (seminorm_tail_le p G X m hC hm hX v hv)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem exists_model_with_tail_error (p : FiniteProbabilityWeights Ω) (G : Finset Ω)
    (X : Seminorm ℂ (Ω → ℂ)) (m : Ω → ℝ) {S : Set (Ω → ℂ)}
    (hS : Balanced ℂ S) (hSn : S.Nonempty) (hSbound : ∀ Q ∈ S, ∀ x, ‖Q x‖ ≤ 1)
    {C C₀ M beta tau : ℝ} (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hM : 0 < M) (hbeta : 0 < beta) (htau : 0 < tau)
    (hm : ∀ x, 0 ≤ m x) (hgood : ∀ x ∈ G, m x ≤ C₀)
    (hX : ∀ v, X v ≤ C * p.mean (fun x => m x * ‖v x‖))
    (hdetect : ∀ psi : Ω → ℂ, (∀ x, ‖psi x‖ ≤ C * C₀ / tau) →
      tau / M ^ 2 ≤ X psi → ∃ Q ∈ S, beta ≤ ‖p.correlation psi Q‖)
    (b : Ω → ℂ) (hb : ∀ x, ‖b x‖ ≤ M) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (Ω → ℂ)) (c : Fin n → ℝ) (e : Ω → ℂ),
      (∀ i, Q i ∈ S) ∧ b = (∑ i, c i • Q i) + e ∧
      (∑ i, |c i|) ≤ 2 / beta ∧
      X e ≤ 2 * tau + C * (M + 2 / beta) *
        p.mean (fun x => if x ∈ G then 0 else m x) ∧
      (n : ℝ) ≤ 1 + 4 * (C * C₀) ^ 2 / (beta ^ 2 * tau ^ 2) := by
  have hK : 0 ≤ C * C₀ := mul_nonneg hC hC₀
  have hR : 0 ≤ 2 / beta := by positivity
  have htail : 0 ≤ p.mean (fun x => if x ∈ G then 0 else m x) :=
    p.mean_nonneg (fun x => by split_ifs; exact le_rfl; exact hm x)
  by_cases hG : 0 < p.mass G
  · let XG := X.comp (finiteMask G)
    have hXG (v : Ω → ℂ) : XG v ≤
        (C * C₀) * (p.condition G hG).mean (fun x => ‖v x‖) :=
      seminorm_mask_le_condition p G hG X m hC hC₀ hX hgood v
    have hdetG (psi : Ω → ℂ) (hpsi : ∀ x, ‖psi x‖ ≤ C * C₀ / tau)
        (hlarge : tau / M ^ 2 ≤ XG psi) :
        ∃ Q ∈ S, beta ≤ ‖(p.condition G hG).correlation psi Q‖ := by
      have hmask : ∀ x, ‖finiteMask G psi x‖ ≤ C * C₀ / tau := by
        intro x
        by_cases hx : x ∈ G
        · simpa [hx] using hpsi x
        · simpa [hx] using div_nonneg hK htau.le
      obtain ⟨Q, hQ, hcorr⟩ := hdetect (finiteMask G psi) hmask hlarge
      refine ⟨Q, hQ, hcorr.trans ?_⟩
      rw [p.norm_correlation_mask G hG]
      exact mul_le_of_le_one_left (norm_nonneg _) (p.mass_le_one G)
    obtain ⟨n, hn, Q, c, e, hQ, hdecomp, hc, he, hlen⟩ :=
      exists_weighted_model_of_detector (p.condition G hG) XG hS hSn hSbound
        hK hM hbeta htau hXG hdetG b hb
    refine ⟨n, hn, Q, c, e, hQ, hdecomp, hc, ?_, hlen⟩
    have herror := model_error_norm_le hb (fun i => hSbound (Q i) (hQ i)) hdecomp hc
    have hglobal := seminorm_le_mask_add_tail p G X m hC hm hX e herror
    exact hglobal.trans (add_le_add he le_rfl)
  · have hmass : p.mass G = 0 := le_antisymm (le_of_not_gt hG) (p.mass_nonneg G)
    obtain ⟨Q₀, hQ₀⟩ := hSn
    refine ⟨1, by decide, fun _ => Q₀, fun _ => 0, b, fun _ => hQ₀, ?_, ?_, ?_, ?_⟩
    · simp
    · simpa using hR
    · have hmask : X (finiteMask G b) ≤ 0 := by
        have h := seminorm_mask_le p G X m hC hC₀ hX hgood b
        simpa [p.mean_mask_zero G hmass] using h
      have hglobal := seminorm_le_mask_add_tail p G X m hC hm hX b hb
      have hmono : C * M * p.mean (fun x => if x ∈ G then 0 else m x) ≤
          C * (M + 2 / beta) * p.mean (fun x => if x ∈ G then 0 else m x) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hR) hC) htail
      linarith
    · have hnonneg : 0 ≤ 4 * (C * C₀) ^ 2 / (beta ^ 2 * tau ^ 2) := by positivity
      simpa using (le_add_of_nonneg_right hnonneg : (1 : ℝ) ≤ 1 + _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.JointProductiveMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (μ : Measure C) (law : C → FiniteProbabilityWeights Ω)
variable (hweight : ∀ x, Measurable (fun c => (law c).weight x))

include hweight

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem centeredFinite_weight_integrable [IsFiniteMeasure μ] (x : Ω) :
    Integrable (fun c => (law c).weight x) μ :=
  Integrable.of_bound (hweight x).aestronglyMeasurable 1 (ae_of_all μ (fun c => by
    rw [Real.norm_of_nonneg ((law c).nonneg x)]
    exact centeredFiniteWeightDensity_le_one law (c, x)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CenteredFiniteSliceResidualEnvelope
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable (μ : Measure C) [IsProbabilityMeasure μ]
variable (law : C → FiniteProbabilityWeights Ω)
variable (hweight : ∀ z, Measurable (fun c => (law c).weight z))

noncomputable def centeredFiniteMarginal : FiniteProbabilityWeights Ω where
  weight z := ∫ c, (law c).weight z ∂μ
  nonneg z := integral_nonneg (fun c => (law c).nonneg z)
  total := by
    rw [← integral_finsetSum _ (fun z _ => centeredFinite_weight_integrable μ law hweight z)]
    simp only [FiniteProbabilityWeights.total, integral_const, probReal_univ, one_smul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ContainedProgressionCubeLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {K α : Type*} [Fintype K] [DecidableEq K] [Fintype α] [DecidableEq α]
variable (L H step : K → ℕ) (c : K → ℤ) (hL : ∀ k, 0 < L k) (hH : ∀ k, 0 < H k)
variable (hsubset : ∀ k, integerProgressionSupport (c k) (step k : ℤ) (H k) ⊆
  Finset.Ico (0 : ℤ) (L k : ℤ))

noncomputable def containedProgressionCubeLaw :
    FiniteProbabilityWeights (∀ k, IntegerScalarCubeBox α (L k)) :=
  (FiniteProbabilityWeights.pi (fun k => integerScalarCubeWeights α (H k) (hH k))).fiberLaw
    (fun y k => containedProgressionCubeMap α (L k) (H k) (step k) (c k) (hL k) (hsubset k) (y k))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.IdealInvariantNiltestBudget
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d n : ℕ}
  (D : RationalFilteredNilmanifold L s d) (I : LieIdeal ℚ L)
  (hI : D.filtration.layer (t + 1) ≤ I.toSubmodule)
  (Q : RationalFilteredNilmanifold (L ⧸ I) t n)
  (hQF : Q.filtration = D.filtration.quotientLie I hI)

theorem idealQuotientOrbit_eval {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    Q.filtration.realification.polynomialOrbitEval w x (D.idealQuotientOrbit I hI Q hQF g) =
      realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I)
        (D.filtration.realification.polynomialOrbitEval w x g) :=
  D.filtration.realQuotientPolynomialOrbit_eval I hI g x

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ I))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ I))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ I))] [T2Space (ℝ ⊗[ℚ] (L ⧸ I))]

theorem exists_idealInvariant_niltest
    (hQL : Q.lattice = D.lattice.map (D.filtration.quotientStepHom I hI))
    {w : σ → ℕ} (T : D.Niltest w)
    (hinv : ∀ z : D.RealGroup, z.coord ∈ I.toSubmodule.baseChange ℝ → ∀ x,
      T.observable (z • x) = T.observable x)
    (H : ℕ) (hH : 1 ≤ H)
    (he : ∀ i j, RationalHeightLE (Q.basis.repr (lieQuotientMap I (D.basis j)) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants Q.basis i j k) H) :
    ∃ S : Q.Niltest w,
      S.orbit = D.idealQuotientOrbit I hI Q hQF T.orbit ∧
      S.normBound = T.normBound ∧
      S.lipBound = rationalReconstructionLipschitzBound t d n H T.lipBound T.normBound ∧
      (∀ x : D.RealGroup, S.observable (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I) x)) =
        T.observable (QuotientGroup.mk x)) ∧
      (∀ x, S.eval x = T.eval x) ∧
      (T.UnitIntervalValued → S.UnitIntervalValued) := by
  have hcover : Q.lattice ≤ D.lattice.map
      (mapOfSteps (hL := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I)) := by
    rw [hQL]
    exact le_rfl
  obtain ⟨f, hf, hfLip, hfBound⟩ := exists_lipschitz_realification_reconstruction
    D.basis Q.basis (lieQuotientMap I) (lieQuotientMap_surjective I) D.lattice Q.lattice hcover
    D.grid Q.grid H D.grid_pos Q.grid_pos hH D.outer_grid Q.outer_grid he hc
    T.observable (fun k hk x => hinv k (by
      apply (realification_mkQ_eq_zero_iff I.toSubmodule k.coord).mp
      exact congrArg (fun z : Q.RealGroup => z.coord) (MonoidHom.mem_ker.mp hk))
      (QuotientGroup.mk x)) T.lipBound T.normBound T.lipschitz T.norm_le
  let S : Q.Niltest w := {
    orbit := D.idealQuotientOrbit I hI Q hQF T.orbit
    observable := f
    normBound := T.normBound
    lipBound := rationalReconstructionLipschitzBound t d n H T.lipBound T.normBound
    norm_le := hfBound
    lipschitz := by
      let : MetricSpace (Q.RealGroup ⧸ Q.lattice.map realificationHom) :=
        realificationQuotientMetricSpace Q.basis Q.lattice Q.grid Q.grid_pos Q.outer_grid
      exact hfLip.weaken (by simp only [Fintype.card_fin]; exact le_rfl) }
  refine ⟨S, rfl, rfl, rfl, hf, ?_, ?_⟩
  · intro x
    exact (congrArg (fun z : Q.RealGroup => f (QuotientGroup.mk z))
      (D.idealQuotientOrbit_eval I hI Q hQF T.orbit x)).trans (hf _)
  · intro hT z
    induction z using Quotient.inductionOn with
    | h z =>
      obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective ℝ (lieQuotientMap_surjective I) z.coord
      let g : D.RealGroup := ⟨x⟩
      have hg : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I) g = z :=
        NilpotentLieBCHGroup.ext hx
      have hfg := hf g
      rw [hg] at hfg
      change (f (QuotientGroup.mk z)).im = 0 ∧ 0 ≤ (f (QuotientGroup.mk z)).re ∧
        (f (QuotientGroup.mk z)).re ≤ 1
      rw [hfg]
      exact hT (QuotientGroup.mk g)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem withUnitBound_complexity (T : D.Niltest w) (hcap : ∀ x, ‖T.observable x‖ ≤ 1)
    {p : ℝ} (hT : T.ComplexityLE p) : (T.withUnitBound hcap).ComplexityLE (p + 1) := by
  refine ⟨hT.1.mono D (by linarith), ?_⟩
  change Real.log (2 + 1 + (T.lipBound : ℝ)) ≤ p + 1
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  rw [Real.exp_add]
  have h := T.observable_budget hT
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_nonneg p)
  nlinarith [T.normBound.coe_nonneg, T.lipBound.coe_nonneg]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  (T : D.Niltest w) (hT : T.UnitIntervalValued)
  (psi : D.Space → ℝ) (hpsi : ∀ z, 0 ≤ psi z ∧ psi z ≤ 1)
  (K : ℝ≥0) (hLip : letI := D.metricSpace; LipschitzWith K psi)

noncomputable def positiveLocalization : D.Niltest w where
  orbit := T.orbit
  observable z := (((T.observable z).re * psi z : ℝ) : ℂ)
  normBound := 1
  lipBound := T.lipBound + K
  norm_le z := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hT z).2.1 (hpsi z).1)]
    exact (mul_le_of_le_one_right (hT z).2.1 (hpsi z).2).trans (hT z).2.2
  lipschitz := by
    let := D.metricSpace
    have ht : LipschitzWith T.lipBound (fun z => (T.observable z).re) := by
      simpa only [one_mul, Function.comp_def, RCLike.re_eq_complex_re] using
        (RCLike.lipschitzWith_re (K := ℂ)).comp T.lipschitz
    have hproduct := bounded_weight_cutoff_lipschitz (fun z => (T.observable z).re) psi
      (B := 1)
      (fun z => by rw [abs_of_nonneg (hT z).2.1]; exact (hT z).2.2)
      (fun z => by rw [abs_of_nonneg (hpsi z).1]; exact (hpsi z).2) ht hLip
    simpa only [one_mul, Function.comp_def] using Complex.isometry_ofReal.lipschitz.comp hproduct

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct NNReal

theorem exists_idealInvariant_niltest_budget (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {s d n : ℕ} (D : RationalFilteredNilmanifold L s d) (I : LieIdeal ℚ L)
      [TopologicalSpace (ℝ ⊗[ℚ] (L ⧸ I))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ I))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (L ⧸ I))] [T2Space (ℝ ⊗[ℚ] (L ⧸ I))]
      (hI : D.filtration.layer (t + 1) ≤ I.toSubmodule)
      (Q : RationalFilteredNilmanifold (L ⧸ I) t n)
      (hQF : Q.filtration = D.filtration.quotientLie I hI)
      (_hQL : Q.lattice = D.lattice.map (D.filtration.quotientStepHom I hI))
      {w : σ → ℕ} (T : D.Niltest w) (p : ℝ),
      0 ≤ p → T.ComplexityLE p → Q.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap I (D.basis j)) i) ≤ p) →
      (∀ z : D.RealGroup, z.coord ∈ I.toSubmodule.baseChange ℝ → ∀ x,
        T.observable (z • x) = T.observable x) →
      ∃ S : Q.Niltest w, S.orbit = D.idealQuotientOrbit I hI Q hQF T.orbit ∧
        S.normBound = T.normBound ∧ S.ComplexityLE ((p + 2) ^ C) ∧
        (∀ x : D.RealGroup, S.observable (QuotientGroup.mk
          (NilpotentLieBCHGroup.realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I) x)) =
          T.observable (QuotientGroup.mk x)) ∧
        (∀ x, S.eval x = T.eval x) ∧ (T.UnitIntervalValued → S.UnitIntervalValued) := by
  obtain ⟨a, _, hcost⟩ := exists_rationalReconstructionLipschitzBound_exp t
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    ((X + 1 + Polynomial.C a) ^ a + X + 4)
  refine ⟨C, hC, ?_⟩
  intro L σ _ _ _ _ _ _ s d n D I _ _ _ _ hI Q hQF hQL w T p hp hT hQ he hinv
  let H := ⌈Real.exp p⌉₊
  obtain ⟨S, hSo, hSn, hSl, hObs, hSe, hPos⟩ := D.exists_idealInvariant_niltest I hI Q hQF hQL T hinv H
    (one_le_ceil_exp p) (fun i j => rationalHeightLE_ceil_exp (he i j))
    (fun i j k => rationalHeightLE_ceil_exp (hQ.2.2.1 i j k))
  have hB : (T.normBound : ℝ) ≤ Real.exp p := by
    linarith [T.observable_budget hT, T.lipBound.coe_nonneg]
  have hL : (T.lipBound : ℝ) ≤ Real.exp p := by
    linarith [T.observable_budget hT, T.normBound.coe_nonneg]
  have hpp : Real.exp p ≤ Real.exp (p + 1) := Real.exp_le_exp.mpr (by linarith)
  let r := (p + 1 + a) ^ a
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hK : (S.lipBound : ℝ) ≤ Real.exp r := by
    rw [hSl]
    exact hcost d n H T.lipBound T.normBound (p + 1) (by linarith)
      (hT.1.1.trans (by linarith)) (hQ.1.trans (by linarith))
      (ceil_exp_le_exp_add_one hp) (hL.trans hpp) (hB.trans hpp)
  have hnum : 2 + (S.normBound : ℝ) + (S.lipBound : ℝ) ≤ Real.exp (r + p + 4) := by
    have hSn' : (S.normBound : ℝ) ≤ Real.exp (r + p) := by
      rw [hSn]
      exact hB.trans (Real.exp_le_exp.mpr (by linarith))
    have hSl' : (S.lipBound : ℝ) ≤ Real.exp (r + p) :=
      hK.trans (Real.exp_le_exp.mpr (by linarith))
    calc
      _ ≤ 4 * Real.exp (r + p) := by linarith [Real.one_le_exp (show 0 ≤ r + p by linarith)]
      _ ≤ Real.exp 4 * Real.exp (r + p) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hbound : r + p + 4 ≤ (p + 2) ^ C := by
    simpa [r, X, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨S, hSo, hSn, ⟨hQ.mono Q ((by linarith : p ≤ r + p + 4).trans hbound), ?_⟩,
    hObs, hSe, hPos⟩
  exact ((Real.log_le_iff_le_exp (by positivity)).mpr hnum).trans hbound

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeChartKernel
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} (T : D.Niltest w)

variable (hT : T.UnitIntervalValued) (phi : OpenPartialHomeomorph (Fin d → ℝ) D.Space)
  (K r : ℝ≥0) (hr : 0 < r) (hr1 : r ≤ 1)
  (hsource : phi.source = {v | ∀ i, |v i| < (r : ℝ)})
  (hinner : tsupport T.observable ⊆ phi '' Metric.closedBall 0 (3 * (r : ℝ) / 4))
  (hForward : letI := D.metricSpace; LipschitzOnWith K phi phi.source) (hgrid : 4 ≤ D.grid)

noncomputable def chartKernel : PatchKernel d := by
  let := D.metricSpace
  exact scaledChartKernel phi (fun x => (T.observable x).re) T.lipBound K r hr hr1
    (fun x => (hT x).2) T.realObservable_lipschitz hsource
    (T.realObservable_tsupport.trans hinner) hForward D.grid hgrid

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestAffineProjection
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

theorem substitute_scalarAffinePolynomial {σ V : Type*} [AddCommGroup V] [Module ℚ V]
    (r : ℚ) (shift : σ → ℚ) (p : VectorPolynomial σ ℚ V) :
    substitute (scalarAffinePolynomial r shift) p =
      weightedDilation (fun _ => 1) r (translate shift p) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval_zero
  intro x
  rw [map_sub, eval_substitute, eval_weightedDilation, eval_translate]
  simp [scalarAffinePolynomial, add_comm]

end VectorPolynomial

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.NativeGridRightDictionary
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_bounded_native_grid_enumeration
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (m : ℕ) (hm : 0 < m)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ n : ℕ, 0 < n ∧ n ≤ (2 * ⌈(m : ℝ) * B⌉₊ + 1) ^ d ∧
      ∃ rep : Fin n → D.RealGroup,
        (∀ j, (∀ i, |(D.basis.baseChange ℝ).repr (rep j).coord i| ≤ B) ∧
          (D.basis.baseChange ℝ).equivFun (rep j).coord ∈ realDenominatorGrid m) ∧
        ∀ g : D.RealGroup,
          (∀ i, |(D.basis.baseChange ℝ).repr g.coord i| ≤ B) →
          (D.basis.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid m →
          ∃ j, g = rep j := by
  classical
  let A : Set (Fin d → ℝ) :=
    {x | (∀ i, |x i| ≤ B) ∧ x ∈ realDenominatorGrid m}
  obtain ⟨hAfin, hAcard⟩ := finite_card_real_grid_box A m ⌈(m : ℝ) * B⌉₊ hm
    (fun _ hx => hx.2) (fun _ hx => hx.1) (Nat.le_ceil _)
  let S : Set D.RealGroup :=
    {g | (∀ i, |(D.basis.baseChange ℝ).repr g.coord i| ≤ B) ∧
      (D.basis.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid m}
  let f : D.RealGroup → (Fin d → ℝ) :=
    fun g => (D.basis.baseChange ℝ).equivFun g.coord
  have hf : Function.Injective f := by
    intro g h hgh
    apply NilpotentLieBCHGroup.ext
    exact (D.basis.baseChange ℝ).equivFun.injective hgh
  have hmaps : Set.MapsTo f S A := by
    intro g hg
    exact ⟨by simpa only [f, Basis.equivFun_apply] using hg.1, hg.2⟩
  have hSfin : S.Finite := Set.Finite.of_injOn hmaps hf.injOn hAfin
  have hScard : S.ncard ≤ (2 * ⌈(m : ℝ) * B⌉₊ + 1) ^ d := by
    exact (Set.ncard_le_ncard_of_injOn f hmaps hf.injOn hAfin).trans
      (by simpa only [Fintype.card_fin] using hAcard)
  let : Fintype S := hSfin.fintype
  have hone : (1 : D.RealGroup) ∈ S := by
    constructor
    · simpa only [coord_one, map_zero, Finsupp.zero_apply, abs_zero] using
        fun _ : Fin d => hB
    · change (D.basis.baseChange ℝ).equivFun (0 : ℝ ⊗[ℚ] L) ∈ _
      rw [map_zero]
      exact ⟨0, by ext i; simp⟩
  let : Nonempty S := ⟨⟨1, hone⟩⟩
  let e := Fintype.equivFin S
  refine ⟨Fintype.card S, Fintype.card_pos, ?_, fun j => (e.symm j).val,
    fun j => (e.symm j).property, ?_⟩
  · simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using hScard
  · intro g hbound hgrid
    let x : S := ⟨g, hbound, hgrid⟩
    exact ⟨e x, (congrArg Subtype.val (e.symm_apply_apply x)).symm⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct

namespace NativeGridRightDictionary

theorem labeling
    {X L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d m : ℕ} {B : ℝ}
    {D : RationalFilteredNilmanifold L s d}
    (dictionary : NativeGridRightDictionary D m B) (rightAt : X → D.RealGroup)
    (hgrid : ∀ x, (D.basis.baseChange ℝ).equivFun (rightAt x).coord ∈
      realDenominatorGrid m) :
    ∃ label : X → Fin dictionary.count, ∀ x,
      (∃ γ ∈ D.realLattice, rightAt x = dictionary.representative (label x) * γ) ∧
      ∀ g : D.RealGroup,
        (QuotientGroup.mk (g * rightAt x) : D.Space) =
          QuotientGroup.mk (g * dictionary.representative (label x)) := by
  classical
  choose label γ hγ heq using fun x => dictionary.cover (rightAt x) (hgrid x)
  refine ⟨label, fun x => ⟨⟨γ x, hγ x, heq x⟩, ?_⟩⟩
  intro g
  rw [heq x, ← mul_assoc]
  exact QuotientGroup.mk_mul_of_mem _ (hγ x)

end NativeGridRightDictionary

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformControlledNativeExternalNetsOfRecovery
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X Y : Type*} [Nonempty X] [PseudoMetricSpace Y]
  (φ : X → Y) (L : ℝ≥0)

theorem positiveImageExtension_lipschitz (f : X → ℂ) (hf : ∀ x, 0 ≤ (f x).re) :
    LipschitzWith L (positiveImageExtension φ L f) := by
  unfold positiveImageExtension
  have h := positiveClip_lipschitz.comp
    (Complex.isometry_ofReal.lipschitz.comp (mcShaneEnvelope_lipschitz φ L _ hf))
  simpa only [Function.comp_def, one_mul] using h

theorem positiveImageExtension_bound_of_reconstruction (f : X → ℂ) (v : Y → ℂ)
    (hv : LipschitzWith L v) (heval : ∀ x, v (φ x) = f x)
    (hf : ∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re ∧ (f x).re ≤ 1) :
    LipschitzWith L (positiveImageExtension φ L f) ∧
      (∀ y, (positiveImageExtension φ L f y).im = 0 ∧
        0 ≤ (positiveImageExtension φ L f y).re ∧ (positiveImageExtension φ L f y).re ≤ 1) ∧
      (∀ y, ‖positiveImageExtension φ L f y‖ ≤ 1) ∧
      ∀ x, positiveImageExtension φ L f (φ x) = f x := by
  refine ⟨positiveImageExtension_lipschitz φ L f (fun x => (hf x).2.1),
    positiveImageExtension_unit_interval φ L f, positiveImageExtension_norm_le_one φ L f, ?_⟩
  apply positiveImageExtension_eq φ L f hf
  intro x z
  simpa only [dist_eq_norm, heval] using hv.dist_le_mul (φ x) (φ z)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {X Y Z : Type*} [Nonempty X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
  (φ : X → Y × Z) (L : ℝ≥0)

theorem positiveImageSlice_lipschitz (f : X → ℂ) (hf : ∀ x, 0 ≤ (f x).re) (z : Z) :
    LipschitzWith L (positiveImageSlice φ L f z) := by
  apply LipschitzWith.of_dist_le_mul
  intro y y'
  have h := (positiveImageExtension_lipschitz φ L f hf).dist_le_mul (y, z) (y', z)
  simpa only [positiveImageSlice, Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using h

theorem positiveImageSlice_parameter_bound (f g : X → ℂ)
    (hf : ∀ x, 0 ≤ (f x).re) (hg : ∀ x, 0 ≤ (g x).re)
    {δ : ℝ} (hfg : ∀ x, ‖f x - g x‖ ≤ δ) (z z' : Z) (y : Y) :
    ‖positiveImageSlice φ L f z y - positiveImageSlice φ L g z' y‖ ≤
      δ + L * dist z z' := by
  have hleft := positiveImageExtension_nonexpansive φ L f g hf hg hfg (y, z)
  have hright : ‖positiveImageSlice φ L g z y - positiveImageSlice φ L g z' y‖ ≤
      L * dist z z' := by
    have h := (positiveImageExtension_lipschitz φ L g hg).dist_le_mul (y, z) (y, z')
    simpa only [positiveImageSlice, Prod.dist_eq, dist_self, max_eq_right dist_nonneg,
      dist_eq_norm] using h
  exact (norm_sub_le_norm_sub_add_norm_sub (positiveImageSlice φ L f z y) (positiveImageSlice φ L g z y)
    (positiveImageSlice φ L g z' y)).trans (add_le_add hleft hright)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {X Y Z : Type*} [Nonempty X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
  (φ : X → Y × Z) (K : ℝ≥0) (f : X → ℂ)
  (hf : ∀ x, 0 ≤ (f x).re)
  (hrecovery : ∀ x, positiveImageSlice φ K f (φ x).2 (φ x).1 = f x)

include hf hrecovery

theorem positiveImageExtension_reconstructs_of_positiveImageSlice_eq :
    LipschitzWith K (positiveImageExtension φ K f) ∧
      ∀ x, positiveImageExtension φ K f (φ x) = f x := by
  refine ⟨positiveImageExtension_lipschitz φ K f hf, ?_⟩
  intro x
  simpa only [positiveImageSlice, Prod.mk.eta] using hrecovery x

theorem exists_lipschitz_reconstruction_of_positiveImageSlice_eq :
    ∃ (v : Y × Z → ℂ) (K' : ℝ≥0), K' ≤ K ∧ LipschitzWith K' v ∧
      ∀ x, v (φ x) = f x := by
  exact ⟨positiveImageExtension φ K f, K, le_rfl,
    positiveImageExtension_reconstructs_of_positiveImageSlice_eq φ K f hf hrecovery⟩

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_external_test_net {O A R X Y Z IO IA IZ : Type*}
    [Nonempty X] [PseudoMetricSpace A] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    [Fintype IO] [Fintype IA] [Fintype R] [Fintype IZ]
    (φ : X → Y × Z) (F : O → A → R → X → ℂ) (L M : ℝ≥0)
    (hpositive : ∀ o a r x, (F o a r x).im = 0 ∧ 0 ≤ (F o a r x).re ∧ (F o a r x).re ≤ 1)
    (hreconstruct : ∀ o a r, ∃ (v : Y × Z → ℂ) (K : ℝ≥0), K ≤ L ∧ LipschitzWith K v ∧
      ∀ x, v (φ x) = F o a r x)
    (hvariation : ∀ o a a' r x, ‖F o a r x - F o a' r x‖ ≤ M * dist a a')
    (oc : IO → O) (ac : IA → A) (zc : IZ → Z) {δO δA δZ : ℝ}
    (hO : ∀ o, ∃ i, ∀ a r x, ‖F o a r x - F (oc i) a r x‖ ≤ δO)
    (hA : ∀ a, ∃ i, dist a (ac i) ≤ δA) (hZ : ∀ z, ∃ i, dist z (zc i) ≤ δZ) :
    let n := Fintype.card IO * Fintype.card IA * Fintype.card R * Fintype.card IZ
    ∃ centers : Fin n → Y → ℂ,
      (∀ i, LipschitzWith L (centers i)) ∧
      (∀ i y, (centers i y).im = 0 ∧ 0 ≤ (centers i y).re ∧ (centers i y).re ≤ 1) ∧
      (∀ i y, ‖centers i y‖ ≤ 1) ∧
      (∀ o a r x, positiveImageSlice φ L (F o a r) (φ x).2 (φ x).1 = F o a r x) ∧
      ∀ o a r z, ∃ i, ∀ y,
        ‖positiveImageSlice φ L (F o a r) z y - centers i y‖ ≤ δO + M * δA + L * δZ := by
  classical
  let I := IO × IA × R × IZ
  let n := Fintype.card IO * Fintype.card IA * Fintype.card R * Fintype.card IZ
  have hcard : Fintype.card I = n := by simp only [I, n, Fintype.card_prod, Nat.mul_assoc]
  let e : I ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let centers : Fin n → Y → ℂ := fun i =>
    positiveImageSlice φ L (F (oc (e.symm i).1) (ac (e.symm i).2.1) (e.symm i).2.2.1)
      (zc (e.symm i).2.2.2)
  refine ⟨centers, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact positiveImageSlice_lipschitz φ L _ (fun x => (hpositive _ _ _ x).2.1) _
  · intro i y
    exact positiveImageExtension_unit_interval φ L _ _
  · intro i y
    exact positiveImageExtension_norm_le_one φ L _ _
  · intro o a r x
    obtain ⟨v, K, hK, hv, heval⟩ := hreconstruct o a r
    exact (positiveImageExtension_bound_of_reconstruction φ L (F o a r) v
      (hv.weaken hK) heval (hpositive o a r)).2.2.2 x
  · intro o a r z
    obtain ⟨io, hio⟩ := hO o
    obtain ⟨ia, hia⟩ := hA a
    obtain ⟨iz, hiz⟩ := hZ z
    refine ⟨e (io, ia, r, iz), ?_⟩
    intro y
    have hsource : ∀ x, ‖F o a r x - F (oc io) (ac ia) r x‖ ≤ δO + M * δA := by
      intro x
      exact (norm_sub_le_norm_sub_add_norm_sub (F o a r x) (F (oc io) a r x)
        (F (oc io) (ac ia) r x)).trans (add_le_add (hio a r x)
          ((hvariation (oc io) a (ac ia) r x).trans (mul_le_mul_of_nonneg_left hia M.coe_nonneg)))
    have h := (positiveImageSlice_parameter_bound φ L (F o a r) (F (oc io) (ac ia) r)
      (fun x => (hpositive _ _ _ x).2.1) (fun x => (hpositive _ _ _ x).2.1) hsource z (zc iz) y).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hiz L.coe_nonneg))
    simpa only [centers, Equiv.symm_apply_apply] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SourceLatticeCover
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
  (D : RationalFilteredNilmanifold L s d) (hst : s ≤ t)
  (Λ : Subgroup (D.raiseStep hst).filtration.Group)

noncomputable def lowerCoverLattice : Subgroup D.filtration.Group :=
  Λ.map (changeStep (D.raiseStep hst).filtration.lowerCentralSeries_eq_bot
    D.filtration.lowerCentralSeries_eq_bot).toMonoidHom

theorem lowerCoverLattice_coordinates :
    bchSubgroupCoordinates D.basis (D.lowerCoverLattice hst Λ) =
      bchSubgroupCoordinates D.basis Λ :=
  bchSubgroupCoordinates_changeStep _ _ D.basis Λ

theorem lowerCoverLattice_forward :
    D.lowerCoverLattice hst Λ ≤ Λ.comap
      (mapOfSteps (hL := D.filtration.lowerCentralSeries_eq_bot)
        (hM := (D.raiseStep hst).filtration.lowerCentralSeries_eq_bot)
        (LieHom.id : L →ₗ⁅ℚ⁆ L)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  exact hy

theorem lowerCoverLattice_le (hΛ : Λ ≤ (D.raiseStep hst).lattice) :
    D.lowerCoverLattice hst Λ ≤ D.lattice := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  exact D.raiseStep_lattice_back hst (hΛ hy)

variable (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates D.basis Λ)
  (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid N)

noncomputable def loweredCover : RationalFilteredNilmanifold L s d :=
  D.withLattice (D.lowerCoverLattice hst Λ) N hN
    (by rw [D.lowerCoverLattice_coordinates]; exact hin)
    (by rw [D.lowerCoverLattice_coordinates]; exact hout)

theorem loweredCover_geometry {p q : ℝ} (hD : D.GeometryComplexityLE p)
    (hpq : p ≤ q) (hNb : (N : ℝ) ≤ Real.exp q) :
    (D.loweredCover hst Λ N hN hin hout).GeometryComplexityLE q :=
  D.withLattice_geometry _ _ _ _ _ hD hpq hNb

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedFixedPositiveDensity
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (o : OrthonormalBasis I ℝ W)

theorem canonicalMixedDensity_continuous_of_ambient
    (c w : I → ℝ) (f : Fin n → ℝ → ℝ) (p : Fin n → PMF ℤ)
    (hf : ∀ i (k : ℤ), f i ((k : ℝ) / basisAxisScale b i) =
      basisAxisScale b i * (p i k).toReal)
    (hs : ∀ x, mixedCoefficientDensity c w p x ≠ 0 → ∀ d,
      |normalizedLatticePoint W b (orthonormalMixedChart o x) d| ≤ 1 / 4)
    (hc : Continuous (canonicalAmbientTorusDensity W b o c w f)) :
    Continuous (canonicalMixedDensity W b hb o c w p) := by
  apply (QuotientAddGroup.isQuotientMap_mk
    (latticeSection (standardEuclideanLattice D) W).toAddSubgroup).continuous_iff.mpr
  have hlift : Continuous (fun u : W => fun i => (u.val i : UnitAddCircle)) := by
    apply continuous_pi
    intro i
    exact (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((PiLp.continuous_apply 2 _ i).comp continuous_subtype_val)
  have he : canonicalMixedDensity W b hb o c w p ∘ QuotientAddGroup.mk =
      fun u : W => canonicalAmbientTorusDensity W b o c w f
        (fun i => (u.val i : UnitAddCircle)) := by
    funext u
    exact (canonicalAmbientTorusDensity_eq W b hb o c w f p hf hs u).symm
  rw [he]
  exact hc.comp hlift

theorem canonicalArrayDensity_continuous {J : Type*} [Fintype J]
    (c w : I → J → ℝ) (f : J → Fin n → ℝ → ℝ) (p : Fin n → J → PMF ℤ)
    (hf : ∀ j i (k : ℤ), f j i ((k : ℝ) / basisAxisScale b i) =
      basisAxisScale b i * (p i j k).toReal)
    (hs : ∀ j x, mixedCoefficientDensity (fun i => c i j) (fun i => w i j)
      (fun i => p i j) x ≠ 0 → ∀ d,
        |normalizedLatticePoint W b (orthonormalMixedChart o x) d| ≤ 1 / 4)
    (hc : ∀ j, Continuous
      (canonicalAmbientTorusDensity W b o (fun i => c i j) (fun i => w i j) (f j))) :
    Continuous (canonicalArrayDensity W b hb o c w p) := by
  apply continuous_finsetProd
  intro j _
  exact (canonicalMixedDensity_continuous_of_ambient W b hb o _ _ (f j) _
    (hf j) (hs j) (hc j)).comp (continuous_apply j)

end Erdos3

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators

theorem canonicalCoefficientDensity_continuous
    {K : Type*} [Fintype K] {m : ℕ} {J I : Fin m → Type*}
    [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (f : ∀ j : Fin m, BoundedCoefficientExponent K (j.val + 1) → Fin (n j) → ℝ → ℝ)
    (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
    (hf : ∀ j e i (k : ℤ), f j e i ((k : ℝ) / basisAxisScale (b j) i) =
      basisAxisScale (b j) i * (p j i e k).toReal)
    (hs : ∀ j e x, mixedCoefficientDensity (fun i => c j i e) (fun i => w j i e)
      (fun i => p j i e) x ≠ 0 → ∀ d,
        |normalizedLatticePoint (euclideanSubspace (U j)) (b j)
          (orthonormalMixedChart (o j) x) d| ≤ 1 / 4)
    (hc : ∀ j e, Continuous (canonicalAmbientTorusDensity
      (euclideanSubspace (U j)) (b j) (o j) (fun i => c j i e) (fun i => w j i e) (f j e))) :
    Continuous (canonicalCoefficientDensity U b hb o c w p) := by
  apply continuous_finsetProd
  intro j _
  exact (canonicalArrayDensity_continuous _ (b j) (hb j) (o j) (c j) (w j) (f j) (p j)
    (hf j) (hs j) (hc j)).comp
      ((continuous_apply j).comp (euclideanCoefficientEquiv_continuous U))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
variable (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
variable (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
variable (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)

include hC hV hσ1 Cinv hCinv hchart hsmall

theorem allocatedCoefficientDensity_continuous :
    Continuous (allocatedCoefficientDensity B U b hb o hR hσ S) := by
  apply canonicalCoefficientDensity_continuous U b hb o
    (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
    (fun j e i => allocatedLayerIntegerInterpolation B U b S j i e)
    (allocatedLayerIntegerPMFs B U b hR hσ S)
    (fun j e i => (allocatedLayerIntegerInterpolation_spec B U b S hR hσ j i e).1)
    (allocatedLayerColumns_quarter_support B U b hR hσ S o hσ1 Cinv hCinv hchart hsmall)
  intro j e
  exact (allocatedAmbientFactor_bounds B U b S o C V hC hV hR hσ ⟨j, e⟩).2.continuous

theorem allocatedCoefficientDensity_bounds :
    ∀ x, allocatedCoefficientDensity B U b hb o hR hσ S x ∈
      Set.Icc (0 : ℝ) ((allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)) := by
  intro x
  rw [← allocatedCoefficientAmbientDensity_eq B U b hb o S hR hσ hσ1 Cinv hCinv hchart hsmall x]
  exact (allocatedCoefficientAmbientDensity_bounds B U b o S C V hC hV hR hσ).1 _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

universe u v

attribute [local instance] ScalarSiteExpansion.termFinite

namespace ScalarSiteExpansion

variable {S : Type u} [Fintype S]

noncomputable def eval (e : ScalarSiteExpansion.{u,v} S) (y : S → ℤ) (x : S → ℝ) : ℂ :=
  ∑ i, e.coefficient i * ∏ s, e.factor i s (y s : ZMod (e.period i)) (x s)

noncomputable def integerEval (e : ScalarSiteExpansion.{u,v} S) (N : ℕ) (y : S → ℤ) : ℂ :=
  e.eval y (fun s => (y s : ℝ) / N)

end ScalarSiteExpansion
end Erdos3

end

section

namespace Erdos3.ScalarSiteExpansion
open scoped BigOperators NNReal Classical
universe u v
variable {S : Type u} [Fintype S]
attribute [local instance] ScalarSiteExpansion.termFinite

noncomputable def rescale (e : ScalarSiteExpansion.{u,v} S) (c : ℂ) (r : ℝ) : ScalarSiteExpansion.{u,v} S where
  Term := e.Term
  period := e.period
  coefficient i := c * e.coefficient i
  factor i s k x := e.factor i s k (r * x)

end Erdos3.ScalarSiteExpansion

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RelativeSliceFiniteLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace ResidueBoxSlice

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {keep : X → Prop} [DecidablePred keep] {N : X → ℕ} {q : ℕ}

theorem fiberSliceLaw_score {s d : ℕ}
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (hq : 0 < q) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (Q : PolynomialPatch {x // keep x} s d) (f : (X → ℤ) → ℝ) (target : ℝ) :
    (S.fiberSliceLaw hlen fixed hfixed).mean
      (fun x => (f x.val - target) *
        (S.fiberReinsertPatch Q).value (fun i => (x.val i : ℝ))) =
      relativePatchSliceScore S (fun x => f (finiteSplitPoint keep x fixed)) target Q := by
  rw [fiberSliceLaw_mean]
  unfold relativePatchSliceScore
  congr 1
  · ext u
    simp
  · funext u
    change (f (S.fiberIntegerPoint fixed u) - target) *
      (S.fiberReinsertPatch Q).value (fun i => (S.fiberIntegerPoint fixed u i : ℝ)) = _
    rw [fiberReinsertPatch_integerPoint_value S Q hq]
    rfl

end ResidueBoxSlice

theorem RelativePatchSliceConclusion.exists_fiber_law_with_slice
    {X : Type*} [Fintype X] [DecidableEq X] {keep : X → Prop} [DecidablePred keep]
    {s rankBound : ℕ} {N : X → ℕ} {f : (X → ℤ) → ℝ} {target cost : ℝ}
    (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (hN : ∀ k : {x // keep x}, 0 < N k.val)
    (h : RelativePatchSliceConclusion s (fun k : {x // keep x} => N k.val)
      (fun x => f (finiteSplitPoint keep x fixed)) target rankBound cost) :
    ∃ (d : ℕ) (Qfull : PolynomialPatch X s d)
      (law : FiniteProbabilityWeights (integerBox N)),
      d ≤ rankBound ∧ relativePatchComplexity Qfull ≤ cost ∧
      (Qfull.kernel.lip : ℝ) ≤ Real.exp cost ∧
      Real.exp (-cost) ≤ law.mean
        (fun x => (f x.val - target) * Qfull.value (fun i => (x.val i : ℝ))) ∧
      ∃ (q : ℕ), 0 < q ∧
        ∃ (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
          (hlen : ∀ k, 0 < S.length k),
          (∀ k, Real.exp (-cost) * (N k.val : ℝ) ≤ (S.length k : ℝ)) ∧
          law = S.fiberSliceLaw hlen fixed hfixed := by
  obtain ⟨q, hq, S, d, Q, hlength, hd, hcost, hscore⟩ := h
  have hlen : ∀ k, 0 < S.length k := by
    intro k
    exact_mod_cast (mul_pos (Real.exp_pos (-cost))
      (Nat.cast_pos.mpr (hN k))).trans_le (hlength k)
  have hlog : Real.log (1 + (Q.kernel.lip : ℝ)) ≤ cost := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    dsimp only [relativePatchComplexity] at hcost
    linarith
  have hlip : (Q.kernel.lip : ℝ) ≤ Real.exp cost := by
    have hpos : 0 < 1 + (Q.kernel.lip : ℝ) := by positivity
    have he := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log hpos] at he
    linarith
  refine ⟨d, S.fiberReinsertPatch Q, S.fiberSliceLaw hlen fixed hfixed,
    hd, hcost, hlip, ?_, q, hq, S, hlen, hlength, rfl⟩
  rwa [S.fiberSliceLaw_score hlen hq fixed hfixed Q f target]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedPhysicalLongIdealCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

noncomputable def allocatedIdealCoverRadius (C : Fin m → ℝ) (j : Fin m) : ℝ :=
  finiteRowChartRadius (rowSets j).card (Fintype.card (I j)) (C j)
    (allocatedIdealCoverSupport (G := G) B rowSets j)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseCommonStrideCardRatio
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem dense_commonStride_slice_card_ratio {I T : Type*}
    [Fintype I] [DecidableEq I] [Fintype T]
    (e : T → I → ℤ) (he : Function.Injective e) {N : I → ℕ}
    (himage : Finset.univ.image e = integerBox N)
    {p : ℝ} {A : Finset T} (hA : IsDenseCommonStrideBox N p (A.image e)) :
    (Fintype.card T : ℝ) / A.card ≤ Real.exp (p * Fintype.card I) := by
  have hcard : (integerBox N).card = Fintype.card T := by
    rw [← himage, Finset.card_image_of_injective _ he, Finset.card_univ]
  simpa only [hcard, Finset.card_image_of_injective _ he] using hA.card_ratio

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeEqualDimension
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d k : ℕ}

namespace Niltest

variable {σ : Type*} {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem castDimension_unit_interval (T : D.Niltest w) (h : d = k) :
    (T.castDimension h).UnitIntervalValued ↔ T.UnitIntervalValued := by
  cases h
  rfl

end Niltest
end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LieSubalgebraLatticeInnerGrid
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators Matrix TensorProduct

theorem lieSubalgebra_comap_inner_grid_of_columns
    {ι κ L : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    (K : LieSubalgebra ℚ L) (bk : Basis κ ℚ K) (b : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l q : ℕ)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates b Γ)
    (hcolumns : ∀ j, b.equivFun (bk j : L) ∈ denominatorGrid q) :
    scaledIntegerGrid (l * q) ⊆ bchSubgroupCoordinates bk
      (Γ.comap (NilpotentLieBCHGroup.map
        (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) K.incl)) :=
  bchSubgroup_comap_inner_grid_of_columns bk b K.incl Γ l q hinner hcolumns

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeMarkedKernelRepresentatives
namespace OAI

section

namespace Erdos3
open Module
open scoped Classical Matrix

section Linear
variable {ι κ V W : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

noncomputable def basisMatrixKernelEquiv (b : Basis ι ℚ V) (c : Basis κ ℚ W)
    (T : V →ₗ[ℚ] W) :
    LinearMap.ker (LinearMap.toMatrix b c T).mulVecLin ≃ₗ[ℚ] LinearMap.ker T := by
  have hker : LinearMap.ker (LinearMap.toMatrix b c T).mulVecLin =
      (LinearMap.ker T).comap b.equivFun.symm.toLinearMap := by
    ext x
    have heq : LinearMap.toMatrix b c T *ᵥ x = c.equivFun (T (b.equivFun.symm x)) := by
      simpa only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using
        LinearMap.toMatrix_mulVec_repr b c T (b.equivFun.symm x)
    simp only [Submodule.mem_comap, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    rw [heq]
    exact c.equivFun.map_eq_zero_iff
  exact (LinearEquiv.ofEq _ _ hker).trans
    (b.equivFun.symm.ofSubmodule' (LinearMap.ker T))

@[simp] theorem basisMatrixKernelEquiv_repr (b : Basis ι ℚ V) (c : Basis κ ℚ W)
    (T : V →ₗ[ℚ] W) (x : LinearMap.ker (LinearMap.toMatrix b c T).mulVecLin) (i : ι) :
    b.repr (basisMatrixKernelEquiv b c T x : V) i = (x : ι → ℚ) i := by
  change b.repr (b.equivFun.symm (x : ι → ℚ)) i = (x : ι → ℚ) i
  rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

theorem exists_bounded_linearMap_kernel_basis
    (b : Basis ι ℚ V) (c : Basis κ ℚ W) (T : V →ₗ[ℚ] W)
    {H : ℕ} (hH : 1 ≤ H)
    (hT : ∀ i j, RationalHeightLE (c.repr (T (b j)) i) H) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧
      ∃ bk : Basis (Fin r) ℚ (LinearMap.ker T),
        ∀ j i, RationalHeightLE (b.repr (bk j : V) i)
          (rationalKernelHeight (Fintype.card κ) H) := by
  let A := LinearMap.toMatrix b c T
  have hA : ∀ i j, RationalHeightLE (A i j) H := by
    simpa only [A, LinearMap.toMatrix_apply] using hT
  obtain ⟨t, ht, bk, hbk⟩ := exists_bounded_rational_kernel_basis A hH hA
  refine ⟨Module.finrank ℚ (LinearMap.ker A.mulVecLin), ?_,
    bk.map (basisMatrixKernelEquiv b c T), ?_⟩
  · simpa only [Module.finrank_pi, Module.finrank_self, Nat.mul_one] using
      (LinearMap.ker A.mulVecLin).finrank_le
  · intro j i
    simp only [Basis.map_apply]
    rw [basisMatrixKernelEquiv_repr b c T (bk j) i]
    exact (hbk j i).mono (rationalKernelHeight_mono hH ht)

end Linear

section Lie
variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem exists_bounded_lie_kernel_basis
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    {H : ℕ} (hH : 1 ≤ H)
    (hφ : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧
      ∃ bk : Basis (Fin r) ℚ (LinearMap.ker φ.toLinearMap),
        ∀ j i, RationalHeightLE (b.repr (bk j : L) i)
          (rationalKernelHeight (Fintype.card κ) H) :=
  exists_bounded_linearMap_kernel_basis b c φ.toLinearMap hH hφ

theorem exists_lie_kernel_basis_exp_height
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    {H : ℕ} (hHpos : 1 ≤ H)
    (hφ : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧
      ∃ bk : Basis (Fin r) ℚ (LinearMap.ker φ.toLinearMap), ∀ j i,
        ((b.repr (bk j : L) i).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 7) ∧
        ((b.repr (bk j : L) i).den : ℝ) ≤ Real.exp ((p + 2) ^ 7) := by
  obtain ⟨r, hr, bk, hbk⟩ := exists_bounded_lie_kernel_basis b c φ hHpos hφ
  have hbudget := rationalKernelHeight_le_budget (Fintype.card κ) H hp hκ hH
  exact ⟨r, hr, bk, fun j i =>
    ⟨(Nat.cast_le.mpr (hbk j i).1).trans hbudget,
      (Nat.cast_le.mpr (hbk j i).2).trans hbudget⟩⟩

theorem exists_lie_kernel_subalgebra_basis_logHeight
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    {p : ℝ} (hp : 0 ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hφ : ∀ i j, rationalLogHeight (c.repr (φ (b j)) i) ≤ p) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧
      ∃ bk : Basis (Fin r) ℚ φ.ker.toLieSubalgebra, ∀ j i,
        ((b.repr (bk j : L) i).num.natAbs : ℝ) ≤ Real.exp ((p + 3) ^ 7) ∧
        ((b.repr (bk j : L) i).den : ℝ) ≤ Real.exp ((p + 3) ^ 7) := by
  obtain ⟨r, hr, bk, hbk⟩ := exists_lie_kernel_basis_exp_height b c φ (one_le_ceil_exp p)
    (fun i j => rationalHeightLE_ceil_exp (hφ i j))
    (by linarith : 0 ≤ p + 1) (hκ.trans (by linarith))
    (ceil_exp_le_exp_add_one hp)
  refine ⟨r, hr, bk, fun j i => ?_⟩
  rw [show p + 1 + 2 = p + 3 by ring] at hbk
  exact hbk j i

end Lie
end Erdos3

end

section

namespace Erdos3

open Module

section Lie

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem exists_marked_kernel_basis_commonHeight
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    {p : ℝ} (hp : 0 ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hφ : ∀ i j, rationalLogHeight (c.repr (φ (b j)) i) ≤ p) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧
      ∃ bk : Basis (Fin r) ℚ (LinearMap.ker φ.toLinearMap),
        ∀ j i, RationalHeightLE (b.repr (bk j : L) i)
          (markedKernelCommonHeight p) := by
  obtain ⟨r, hr, bk, hbk⟩ :=
    exists_lie_kernel_subalgebra_basis_logHeight b c φ hp hκ hφ
  exact ⟨r, hr, bk, fun j i => rationalHeightLE_ceil_exp_of_entries (hbk j i)⟩

theorem exists_marked_kernel_basis_commonHeight_of_dim
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hφ : ∀ i j, rationalLogHeight (c.repr (φ (b j)) i) ≤ p) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧ (r : ℝ) ≤ p ∧
      ∃ bk : Basis (Fin r) ℚ (LinearMap.ker φ.toLinearMap),
        ∀ j i, RationalHeightLE (b.repr (bk j : L) i)
          (markedKernelCommonHeight p) := by
  obtain ⟨r, hr, bk, hbk⟩ := exists_marked_kernel_basis_commonHeight b c φ hp hκ hφ
  exact ⟨r, hr, (Nat.cast_le.mpr hr).trans hι, bk, hbk⟩

end Lie
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductANOVAEnergyOrder
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

noncomputable def productANOVATruncation (D : Finset (Finset I))
    (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) : ℝ := ∑ S ∈ D, productANOVA μ S f x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RelativePatchRankTightening
namespace OAI

section

namespace Erdos3

theorem RelativePatchSliceConclusion.tighten_rank
    {X : Type*} [Fintype X] {s : ℕ} {N : X → ℕ} {f : (X → ℤ) → ℝ}
    {target cost : ℝ} {rankBound : ℕ}
    (h : RelativePatchSliceConclusion s N f target rankBound cost) :
    RelativePatchSliceConclusion s N f target (min rankBound ⌊cost⌋₊) cost := by
  obtain ⟨q,hq,S,d,A,hlength,hd,hcomplexity,hscore⟩ := h
  have hdp : d ≤ ⌊cost⌋₊ := Nat.le_floor ((relativePatchComplexity_rank_le A).trans hcomplexity)
  exact ⟨q,hq,S,d,A,hlength,le_min hd hdp,hcomplexity,hscore⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BoxNiltestDetection
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct BigOperators

variable {σ L Ω : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L 0 d) {w : σ → ℕ}

theorem norm_correlation_step_zero_sample (T : D.Niltest w)
    (Q : Finset Ω) (x : Ω → (σ → ℤ)) (f : Ω → ℂ) :
    ‖finiteCorrelation Q f (fun a => T.eval (x a))‖ ≤
      (T.normBound : ℝ) * ‖𝔼 a ∈ Q, f a‖ := by
  calc
    _ = ‖𝔼 a ∈ Q, f a‖ * ‖T.observable (QuotientGroup.mk (1 : D.RealGroup))‖ := by
      simp only [finiteCorrelation, eval_step_zero D, ← Finset.expect_mul, norm_mul, norm_star]
    _ ≤ _ := by
      rw [mul_comm (T.normBound : ℝ)]
      exact mul_le_mul_of_nonneg_left (T.norm_le _) (norm_nonneg _)

theorem detection_step_zero_sample (T : D.Niltest w) {p ρ : ℝ}
    (hT : T.ComplexityLE p) (Q : Finset Ω) (x : Ω → (σ → ℤ)) (f : Ω → ℂ)
    (hcorr : ρ ≤ ‖finiteCorrelation Q f (fun a => T.eval (x a))‖) :
    ρ / Real.exp p ≤ ‖𝔼 a ∈ Q, f a‖ := by
  apply (div_le_iff₀ (Real.exp_pos p)).mpr
  have hB : (T.normBound : ℝ) ≤ Real.exp p := by
    have hh := T.observable_budget hT
    linarith [T.lipBound.coe_nonneg]
  have hc := hcorr.trans (norm_correlation_step_zero_sample D T Q x f)
  exact hc.trans (by nlinarith [norm_nonneg (𝔼 a ∈ Q, f a)])

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.SumNilmanifoldFactors
namespace OAI

section

universe u

namespace Erdos3

open scoped TensorProduct

namespace RationalFilteredNilmanifold

variable {ι κ σ : Type*} {L : ι → Type u} {M : κ → Type u}
  [∀ i, LieRing (L i)] [∀ j, LieRing (M j)]
  [∀ i, LieAlgebra ℚ (L i)] [∀ j, LieAlgebra ℚ (M j)] {s : ℕ} {d : ι → ℕ} {e : κ → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (e j))

noncomputable def sumOrbits {w : σ → ℕ}
    (g : ∀ i, (D i).filtration.realification.PolynomialOrbit w)
    (h : ∀ j, (E j).filtration.realification.PolynomialOrbit w) :
    ∀ k : ι ⊕ κ, (sumFactors D E k).filtration.realification.PolynomialOrbit w
  | .inl i => g i
  | .inr j => h j

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.UnitComparisonNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  (T U : D.Niltest w) (hT : ∀ x, ‖T.observable x‖ ≤ 1)
  (hU : ∀ x, ‖U.observable x‖ ≤ 1)

theorem unitComparison_complexity {p : ℝ}
    (hTc : T.ComplexityLE p) (hUc : U.ComplexityLE p) :
    (T.unitComparison U hT hU).ComplexityLE (p + 4) := by
  refine ⟨hTc.1.mono D (by linarith), ?_⟩
  change Real.log (2 + 1 + ((U.lipBound + T.lipBound : ℝ≥0) : ℝ)) ≤ p + 4
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  have hT' := T.observable_budget hTc
  have hU' := U.observable_budget hUc
  calc
    _ ≤ 5 * Real.exp p := by
      simp only [NNReal.coe_add]
      linarith [T.normBound.coe_nonneg, U.normBound.coe_nonneg, Real.exp_nonneg p]
    _ ≤ Real.exp 4 * Real.exp p := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp (p + 4) := by rw [← Real.exp_add, add_comm]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end


