-- Prove2me | Definitions.Def_OAIE3v2B198
-- name    : OAIE3v2B198
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:36:03.882949+00:00
-- url     : https://prove2.me/theorems/e65c5331-5267-489e-83f6-ef9e67c4292b
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 202 of 311
-- statement:
--   Definitions bundle 202 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B178`, `OAIE3v2B299`, `OAIE3v2B180` of this split.
--
--   Modules: `Dynamics/AllocatedFixedScaleCollisionBudget.lean`, `Estimates/AllocatedExternalCandidateOptionJointConclusion.lean`, `Estimates/AllocatedRecoveredPreparedFreeze.lean`, `Estimates/AxisCompression.lean`, `Estimates/CanonicalEmptyLayerGeometry.lean`, `Estimates/CommonMarkedMultidegree.lean`, `Estimates/CoveredInducedCorrelationFamily.lean`, `Estimates/CubicPairFactoredModel.lean`, `Estimates/CubicPairPartitionPrecision.lean`, `Estimates/CubicRootPermutation.lean`, `Estimates/MixedPairPartitionPrecision.lean`, `Estimates/MixedPrimitiveGowers.lean`, `Estimates/NativeAbsorbedIntervals.lean`, `Estimates/ProductiveFrozenLocalMajorFamily.lean`, `Estimates/QuadraticBoundedFamily.lean`, `Estimates/RationalTaggedConstraintHistory.lean`, `Fourier/MajorPhaseLowFourierExtraction.lean`, `Geometry/BoundedCertifiedFullChartMajorIteration.lean`, `Geometry/CertifiedFullChartDecompositionSource.lean`, `Geometry/CertifiedFullChartFrozenTerminal.lean`, `Geometry/FullChartHomogeneousCorrection.lean`, `Geometry/FullTaggedChartCoefficientRange.lean`, `Geometry/InhomogeneousFullChartLift.lean`, `Geometry/MarkedDirectionCoordinates.lean`, `Geometry/TerminalChartSlowEvaluation.lean`, `Lattices/AllocatedRecoveredIntegerFullChart.lean`, `Lattices/IntegerFrozenChart.lean`, `Linear/AllocatedModularRankBadProduct.lean`, `Linear/PositivePhysicalProjectionError.lean`, `Nilpotent/NativeIntegerChartNiltest.lean`, `Polynomial/CubicPairPolynomial.lean`, `Polynomial/PolynomialCoordinateFreezeBounds.lean`, `Probability/PhysicalRowsDensityTransport.lean`, `Sampling/ActualForecastDataNativeProductBudget.lean`, `Sampling/AllocatedExternalCandidateSamplerFamily.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B178
import Definitions.Def_OAIE3v2B299
import Definitions.Def_OAIE3v2B180

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeAbsorbedIntervals
namespace OAI

section

namespace Erdos3.NativeMultilinearIntervalFamily

open scoped BigOperators

variable {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N p f} (B : NativeMultilinearIntervalFamily W q)

noncomputable def intervalSet (t : B.quadruples) : Finset ℤ :=
  Finset.Ico ((B.interval t).start : ℤ) ((B.interval t).start + (B.interval t).length)

end Erdos3.NativeMultilinearIntervalFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MarkedDirectionCoordinates
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial

variable {I ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ)

noncomputable def markedQuotientDirectionLinear :
    RationalTorus.Algebra t →ₗ[ℚ] MarkedShiftQuotient F v w marked t :=
  (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.comp
    (markedShiftDirectionLinear F v w marked t)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonMarkedMultidegree
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

noncomputable def rationalMarkedDirectionMap :
    (Fin t → ℚ) →ₗ[ℚ] (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :=
  rationalLieInclusion.toLinearMap.comp (markedQuotientDirectionLinear F v w marked t)

noncomputable def realMarkedParameterDirection :
    (Fin t → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t) :=
  realDirectionExtension (rationalMarkedDirectionMap F v w marked t)

end Erdos3

end

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

noncomputable def realMarkedParameterElement (a : Fin t → ℝ) :
    (markedShiftMultidegree F v w marked hw hv t).realification.Group :=
  ⟨realMarkedParameterDirection F v w marked t a⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredInducedCorrelationFamily
namespace OAI

section

namespace Erdos3.QuadraticMarked

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

noncomputable def filtration : DegreeRankLieFiltration Seed 1 1 :=
  (RationalTorus.filtration 1).canonicalDegreeRank

noncomputable def generators : Fin 1 → Seed := RationalTorus.basis 1

theorem generator_mem (i : Fin 1) : generators i ∈ filtration.layer (weights i) 1 := by
  change generators i ∈ (RationalTorus.filtration 1).rankLayer 1 1
  rw [NilpotentLieFiltration.rankLayer_one, (RationalTorus.filtration 1).one_eq_top]
  trivial

abbrev Algebra (t : ℕ) := MarkedShiftQuotient filtration generators weights marked t

noncomputable def multidegree (t : ℕ) :
    MultidegreeLieFiltration (Fin 2) (Algebra t) 2 (mixedCorrelationDegree 1) :=
  markedShiftMultidegree filtration generators weights marked weight_pos generator_mem t

end Erdos3.QuadraticMarked

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticBoundedFamily
namespace OAI

section

namespace Erdos3.QuadraticMarked

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

noncomputable def parameter (t : ℕ) (v : Fin t → ℝ) : (multidegree t).realification.Group :=
  realMarkedParameterElement filtration generators weights marked weight_pos generator_mem t v

end Erdos3.QuadraticMarked

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubicRootPermutation
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeSampleCorrelation

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
  {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  (V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift)))

noncomputable def cubicPairFrequencies :
    ∀ k, optionLieSpace V.L (fun _ : Fin 2 => W.L) k →ₗ[ℚ] ℚ
  | none => 0
  | some k => ![-(2 • W.vertical.frequency), 2 • W.vertical.frequency] k

end NativeSampleCorrelation
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CubicPairPolynomial
namespace OAI

section

namespace Erdos3.NativeSampleCorrelation

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
  {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  (V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift)))

noncomputable def cubicPairPolynomial :
    ((pi V.cubicPairModels).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 3 => 1)).Group :=
  let o := NilpotentLieFiltration.piRealOrbit (fun k => (V.cubicPairModels k).filtration)
    (fun k => (V.cubicPairTests k).orbit)
  ⟨⟨o.log, o.property⟩⟩

end Erdos3.NativeSampleCorrelation

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubicPairFactoredModel
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
  (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r)

noncomputable def cubicPairFrozenVector (k : Fin 2)
    (a b : (pi V.cubicPairModels).RealGroup) (out : Fin W.outputDim)
    (x : Fin 3 → ℤ) : ℂ :=
  W.vertical.observable out (productProjection V.cubicPairModels (some k)
    (QuotientGroup.mk (R.frozenMiddleValue a b x)))

end NativePolynomialOrbitFactors

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubicPairPartitionPrecision
namespace OAI

section

namespace Erdos3.NativePolynomialOrbitFactors

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
  (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r)

noncomputable def cubicPairAnchoredVector (y : Fin 3 → ℤ)
    (k : Fin 2) (out : Fin W.outputDim) (x : Fin 3 → ℤ) : ℂ :=
  R.cubicPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x

end Erdos3.NativePolynomialOrbitFactors

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

section Data

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}

structure NativeCubicPairPartition
    (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
      V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
      (fun _ : Fin 3 => (N : ℝ)) r) (b ε : ℝ) where
  I : Type
  [finite : Fintype I]
  card_bound : (Fintype.card (Fin 3 → I) : ℝ) ≤ Real.exp b
  weight : I → ZMod N → ℝ
  positive : ∀ j, PositiveCyclicNiltest.{0} 1 N b (weight j)
  total : ∀ x, ∑ j, weight j x = 1
  anchor : (Fin 3 → I) → (Fin 3 → ZMod N)
  equivalence : ∀ j, NativeIntegerVectorEquivalence 2 b
    (R.cubicPairAnchoredVector (fun k => ((anchor j k).val : ℤ)) 0)
    (R.cubicPairAnchoredVector (fun k => ((anchor j k).val : ℤ)) 1)
  weighted_approximation : ∀ (k : Fin 2) (out : Fin W.outputDim),
    (𝔼 x : Fin 3 → ZMod N,
      ∑ j, (∏ l, weight (j l) (x l) : ℝ) * ‖W.eval out
        (cubicTrilinearInput ((x k.succ).val : ℤ) ((x k.rev.succ).val : ℤ) (((x 0).val : ℤ) + shift)) -
          R.cubicPairAnchoredVector (fun l => ((anchor j l).val : ℤ)) k out
            (fun l => ((x l).val : ℤ))‖) ≤ ε

attribute [local instance] NativeCubicPairPartition.finite

end Data

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPairPartitionPrecision
namespace OAI

section

namespace Erdos3.NativePolynomialOrbitFactors

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)

noncomputable def mixedPairAnchoredVector (y : Fin (n + 2) → ℤ)
    (k : Fin 2) (out : Fin W.outputDim) (x : Fin (n + 2) → ℤ) : ℂ :=
  R.mixedPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x

end Erdos3.NativePolynomialOrbitFactors

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

section Data

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}

structure NativeMixedPairPartition
    (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
      V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
      (fun _ : Fin (n + 2) => (N : ℝ)) r) (b ε : ℝ) where
  I : Type
  [finite : Fintype I]
  card_bound : (Fintype.card (Fin (n + 2) → I) : ℝ) ≤ Real.exp b
  weight : I → ZMod N → ℝ
  positive : ∀ j, PositiveCyclicNiltest.{0} 1 N b (weight j)
  total : ∀ x, ∑ j, weight j x = 1
  anchor : (Fin (n + 2) → I) → (Fin (n + 2) → ZMod N)
  equivalence : ∀ j, NativeIntegerVectorEquivalence (n + 1) b
    (R.mixedPairAnchoredVector (fun k => ((anchor j k).val : ℤ)) 0)
    (R.mixedPairAnchoredVector (fun k => ((anchor j k).val : ℤ)) 1)
  weighted_approximation : ∀ (k : Fin 2) (out : Fin W.outputDim),
    (𝔼 x : Fin (n + 2) → ZMod N,
      ∑ j, (∏ l, weight (j l) (x l) : ℝ) * ‖W.eval out
        (mixedSlotInput ((x (![0, 1] k)).val : ℤ) ((x (![1, 0] k)).val : ℤ)
                  (fun j => ((x j.succ.succ).val : ℤ))) -
          R.mixedPairAnchoredVector (fun l => ((anchor j l).val : ℤ)) k out
            (fun l => ((x l).val : ℤ))‖) ≤ ε

attribute [local instance] NativeMixedPairPartition.finite

end Data

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPrimitiveGowers
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem HasCyclicMixedTargetCorrelation.mixed_sum {d N : ℕ} [NeZero N] {p q : ℝ}
    {f : ZMod N → ℂ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p)
    (H : HasCyclicMixedTargetCorrelation f
      (fun k x => W.eval k (mixedReplicatedInput (x 0) (fun j => x j.succ))) q) :
    ∃ (i : Fin W.outputDim) (A : Fin (d + 3) → (Fin (d + 3) → ZMod N) → ℂ),
      (∀ j x, ‖A j x‖ ≤ 1) ∧ (∀ j, MissesBoxCoordinate (A j) j) ∧
      Real.exp (-q) ≤ ‖𝔼 u : Fin (d + 1) → ZMod N, 𝔼 m : ZMod N, 𝔼 h : ZMod N,
        star (f (m + h + ∑ j, u j)) *
          star (W.eval i (mixedSlotInput (h.val : ℤ) m.val (fun j => (u j).val))) *
            ∏ j, A j (Fin.cons h (Fin.cons m u))‖ := by
  obtain ⟨i, A, hA, hAi, hc⟩ := H
  refine ⟨i, A, hA, ?_, ?_⟩
  · intro j x v
    apply hAi j
    intro k hkj
    exact Function.update_of_ne hkj v x
  · have hvals (m : ZMod N) (u : Fin (d + 1) → ZMod N) :
        (fun j : Fin (d + 2) => (((Fin.cons m u : Fin (d + 2) → ZMod N) j).val : ℤ)) =
          Fin.cons (m.val : ℤ) (fun j => ((u j).val : ℤ)) := by
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    have hmean :
        (𝔼 x : Fin (d + 3) → ZMod N,
          star (f (∑ k, x k)) * star (W.eval i
            (mixedReplicatedInput ((x 0).val : ℤ) (fun j => ((x j.succ).val : ℤ)))) * ∏ j, A j x) =
        𝔼 u : Fin (d + 1) → ZMod N, 𝔼 m : ZMod N, 𝔼 h : ZMod N,
          star (f (m + h + ∑ j, u j)) *
            star (W.eval i (mixedSlotInput (h.val : ℤ) m.val (fun j => (u j).val))) *
              ∏ j, A j (Fin.cons h (Fin.cons m u)) := by
      rw [expect_mixed_tuple]
      apply Finset.expect_congr rfl
      intro u _
      rw [Finset.expect_comm]
      apply Finset.expect_congr rfl
      intro m _
      apply Finset.expect_congr rfl
      intro h _
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hvals, mixedSlotInput,
        add_left_comm, add_assoc]
    exact hc.trans_eq (congrArg norm hmean)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AxisCompression
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def CyclicTranslatedNiltestShiftBound (degree N : ℕ) [NeZero N]
    (p error : ℝ) (a J : ZMod N → ℝ) (E : Finset (ZMod N)) : Prop :=
  ∀ h ∉ E, ∀ f : ZMod N → ℝ, PositiveCyclicNiltest.{0} degree N p f →
    ∀ b : ZMod N, (𝔼 x, a x * J (x + h) * f (b + x)) ≤ error

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateSamplerFamily
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

namespace AllocatedExternalCandidateSamplerFamily

variable {B U b S hb o hR hσ N poly hm τ ξ stride cells}
    (A : AllocatedExternalCandidateSamplerFamily B U b S hb o hR hσ N poly hm τ ξ stride cells)

abbrev Site := (A 0).Site

end AllocatedExternalCandidateSamplerFamily

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem selectedJointFiniteLaw_noninjectivity_le {K I S : Type*}
    [Fintype K] [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
    (A : Finset (I → ℤ)) (hA : A.Nonempty)
    (site : S → K → ℤ) (hsite : Function.Injective site) (i : I)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (T : Finset (ColumnResiduePattern (Option K) I modulus)) (hT : T.Nonempty)
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {L : ℝ} (hL : 0 < L) (hwidth : ∀ k, L ≤ W (some k,i))
    (D : (I → ℤ) → (Option K × I → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass A modulus T W D)
    (hlower : 1/2 ≤ selectedJointDensityMass A modulus T W D)
    {M : ℝ} (hM : 0 ≤ M) (hcap : ∀ a z, D a z ≤ M) :
    (selectedJointFiniteLaw A hA modulus T W hW hZ D hD0 hD).mean
      (fun z => noninjectivityIndicator (fun s => jointIntegerPhysicalSite (site s) (z.1.val,z.2.val))) ≤
        2*M*((Fintype.card S : ℝ)^2*(2*(modulus i : ℝ)/L)) := by
  rw [selectedJointFiniteLaw]
  apply FiniteProbabilityWeights.reweightPositive_noninjectivity_le
    (selectedJointReference A hA modulus T W hW hZ)
    (fun z s => jointIntegerPhysicalSite (site s) (z.1.val,z.2.val))
    (fun z => D z.1.val z.2.val) (fun z => hD0 z.1.val z.2.val)
    (by rw [selectedJointReference_densityMass]; exact hD) hM (fun z => hcap z.1.val z.2.val)
  · rwa [selectedJointReference_densityMass]
  · positivity
  · intro s t hst
    rw [selectedJointReference_collision]
    exact selectedResidue_distinct_collision_le (site s) (site t) (fun h => hst (hsite h)) i
      modulus hmodulus T hT W hW hZ hscale hL hwidth

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedScaleCollisionBudget
namespace OAI

section

namespace Erdos3

namespace BooleanCubeKernel

open scoped BigOperators Classical

theorem selectedJointFiniteLaw_collision_small_with_cap {K X S : Type*}
    [Fintype K] [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]
    (A : Finset (X → ℤ)) (hA : A.Nonempty)
    (site : S → K → ℤ) (hsite : Function.Injective site) (i : X)
    {F P δ : ℝ} (hP : 0 ≤ P) (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
    (hK : (Fintype.card K : ℝ) ≤ P) (hbound : ∀ s k, |(site s k : ℝ)| ≤ Real.exp P)
    (modulus : X → ℕ) (hmodulus : ∀ i, 0 < modulus i) (hmodP : (modulus i : ℝ) ≤ Real.exp P)
    (T : Finset (ColumnResiduePattern (Option K) X modulus)) (hT : T.Nonempty)
    (W : Option K × X → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {ρ N : ℝ} (hρ : 0 < ρ) (hρP : 1/ρ ≤ Real.exp (spatialSamplingBudget P))
    (hN : Real.exp (F + 2*P*(P+5) + spatialSamplingBudget P + 2*P + 4) ≤ N)
    (hwidth : ∀ k, ρ*N ≤ W (some k,i))
    (D : (X → ℤ) → (Option K × X → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass A modulus T W D)
    (hlower : 1/2 ≤ selectedJointDensityMass A modulus T W D)
    (hcap : ∀ a z, D a z ≤ Real.exp F) :
    (selectedJointFiniteLaw A hA modulus T W hW hZ D hD0 hD).mean
      (fun z => noninjectivityIndicator (fun s => jointIntegerPhysicalSite (site s) (z.1.val,z.2.val))) ≤ δ := by
  have hN0 : 0 < N := (Real.exp_pos _).trans_le hN
  have hcollision := selectedJointFiniteLaw_noninjectivity_le A hA site hsite i
    modulus hmodulus T hT W hW hZ hscale (mul_pos hρ hN0) hwidth D hD0 hD hlower
    (Real.exp_pos _).le hcap
  exact hcollision.trans (collision_error_of_exp_size_with_cap (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hρ hδ (integerSites_card_le_exp site hsite hP hK hbound)
    hmodP hρP hδP hN)

end BooleanCubeKernel

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PositivePhysicalProjectionError
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

variable {I K F : Type*} [Fintype I] [Fintype K] [Fintype F] {m q : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (root : K → ℤ) (difference : Fin q → K → ℤ) (D : ℕ)
variable (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
variable (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
variable (hm : ∀ j d, coefficients (p j) d ∈ U j)
variable (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
variable (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ s v, ‖test s v‖ ≤ 1)
variable (base : I → ℤ) (modulus : I → ℕ)
variable (T : Finset (ColumnResiduePattern (Option K) I modulus))
variable (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)

local notation "frame" => (fun z : Option K × I → ℤ => fun k i => (z (k, i) : ℝ))
local notation "output" => physicalCubeRootDifferences root (Matrix.of difference) base
local notation "law" => selectedResidueSmoothPMF modulus T V hV hZ

include hp htest in
theorem selectedResidue_positive_density_projection_error
    (density : CoefficientTorus (K := K) U → ℝ)
    (f : EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    {η δ : ℝ} (hη : 0 ≤ η)
    (happrox : ∀ x, ‖(density x : ℂ) - coefficientTorusFourierSum U frequency c x‖ ≤ η) :
    let pa := fun j => translate (fun i => (base i : ℝ)) (p j)
    let hma := fun j => coefficients_translate_mem (U j) (fun i => (base i : ℝ)) (p j) (hm j)
    ∀ (_hpositive : ∀ z, ‖affineCubeFourierProjection U root difference frequency pa c (frame z) -
      (f (euclideanCoefficientJetMap U root (Matrix.of difference)
        (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
        (affineCoefficientCoverSample U pa hma D (frame z))) : ℂ)‖ ≤ η)
    (_hprojection :
      ‖(∑' z, ((law z).toReal : ℂ) * (physicalCubeSiteTest test (output z) *
        affineCubeFourierSum frequency pa c (frame z))) -
        ∑' z, ((law z).toReal : ℂ) * (physicalCubeSiteTest test (output z) *
          affineCubeFourierProjection U root difference frequency pa c (frame z))‖ ≤ δ),
    ‖(∑' z, ((law z).toReal : ℂ) * (physicalCubeSiteTest test (output z) *
      (density (affineSampleCoefficientTorus U pa hma (frame z)) : ℂ))) -
      ∑' z, ((law z).toReal : ℂ) * physicalCubePositiveTest U D p hm f test (output z)‖ ≤ 2 * η + δ := by
  intro pa hma hpositive hprojection
  have hpa (j) : DegreeLE (1 : I → ℕ) (j.val + 1) (pa j) :=
    degreeLE_translate (1 : I → ℕ) (fun _ => by norm_num) _ (p j) (hp j)
  have happ (z) : ‖(density (affineSampleCoefficientTorus U pa hma (frame z)) : ℂ) -
      affineCubeFourierSum frequency pa c (frame z)‖ ≤ η := by
    have h := happrox (affineSampleCoefficientTorus U pa hma (frame z))
    rw [coefficientTorusFourierSum_sample U frequency c pa hpa hma (frame z)] at h
    exact h
  have hpos (z) : ‖affineCubeFourierProjection U root difference frequency pa c (frame z) -
      (f (physicalCubeEuclideanSample U D p hm (output z)) : ℂ)‖ ≤ η := by
    have h := hpositive z
    rw [coefficientCoverSample_physicalJet U root difference D p hp hm base z] at h
    exact h
  exact selectedResidueSmoothPMF_projection_approximation modulus T V hV hZ
    (fun z => physicalCubeSiteTest test (output z))
    (fun z => (density (affineSampleCoefficientTorus U pa hma (frame z)) : ℂ))
    (fun z => affineCubeFourierSum frequency pa c (frame z))
    (fun z => affineCubeFourierProjection U root difference frequency pa c (frame z))
    (fun z => (f (physicalCubeEuclideanSample U D p hm (output z)) : ℂ))
    hη (fun z _ => physicalCubeSiteTest_norm_le test htest (output z))
    (fun z _ => happ z) (fun z _ => hpos z) hprojection

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PhysicalRowsDensityTransport
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped Classical

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
local notation "Row" => (fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (Fin.val j + 1)})
local notation "Std" => (fun j : Fin m => BoundedBooleanJet (Fin q) (Fin.val j + 1))

variable [CompactSpace (CoefficientTorus (K := Fin q) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
variable [BorelSpace (CoefficientTorus (K := Fin q) U)]
variable (μ : Measure (CoefficientTorus (K := Fin q) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include μ in
theorem physicalRows_projected_density_law {K : Type*} [Fintype K]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (ρ : Measure (CoefficientTorus (K := K) U))
    (root : K → ℤ) (D : Matrix (Fin q) K ℤ) (g : EuclideanJetLayers U Std → ℝ)
    (hlaw : ρ.map (euclideanCoefficientJetMap U root D
      (fun j => (Subtype.val : Std j → Finset (Fin q)))) =
      realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : Std j => ν j))) g) :
    ρ.map (euclideanCoefficientJetMap U root D (fun j => (Subtype.val : Row j → Finset (Fin q)))) =
      realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : Row j => ν j)))
        (fun z => g (physicalRowsToStandard U z)) := by
  let e := physicalRowsStandardEquiv (q := q) U
  have hp : MeasurePreserving e
      (Measure.pi (fun j => Measure.pi (fun _ : Row j => ν j)))
      (Measure.pi (fun j => Measure.pi (fun _ : Std j => ν j))) :=
    physicalRowsToStandard_measurePreserving U μ ν
  have hi := MeasurePreserving.symm e hp
  have hh := congrArg (Measure.map e.symm) hlaw
  rw [Measure.map_map e.symm.measurable
    (euclideanCoefficientJetMap_continuous U root D _).measurable,
    realDensityMeasure_map_equiv, hi.map_eq] at hh
  have he : e.symm ∘ euclideanCoefficientJetMap U root D
      (fun j => (Subtype.val : Std j → Finset (Fin q))) =
      euclideanCoefficientJetMap U root D (fun j => (Subtype.val : Row j → Finset (Fin q))) := by
    funext z
    apply e.injective
    change e (e.symm _) = _
    rw [e.apply_symm_apply]
    exact (physicalRowsToStandard_coefficient U root D z).symm
  rw [he] at hh
  convert hh using 1
  congr! (transparency := .reducible)

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.MajorPhaseLowFourierExtraction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial Module RationalFilteredNilmanifold PolynomialTranslationLie
open scoped TensorProduct NNReal BigOperators

noncomputable def majorPhaseSample {m : ℕ} {X : Type}
    (J : Fin m → Type) [∀ j, Fintype (J j)] (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (F : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
    (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J d)) → ℤ)
    (r : (X → ℤ) → ℂ) (u : X → ℤ) : ℂ :=
  ((Ψ.value (fun i => MvPolynomial.eval (fun x => (u x : ℝ))
      (lowTaggedPolynomial J d poly i) - c i - (β u i : ℝ)) : ℂ) *
    (Real.fourierChar (MvPolynomial.eval (fun j => ((Sum.elim u (β u) j : ℤ) : ℝ)) F) : ℂ)) * r u

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalTaggedConstraintHistory
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]
    {X R S V : Type*} [CommRing R] [CommRing S]
    [AddCommGroup V] [Module R V]

noncomputable def lowTaggedVectorRestrict (k : ℕ) :
    VectorPolynomial (X ⊕ (Σ j, J j)) R V →ₗ[R]
      VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V :=
  (lowTaggedRestrict (X := X) (R := R) J k).toLinearMap.rTensor V

noncomputable def lowTaggedVectorExtend (k : ℕ) :
    VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V →ₗ[R]
      VectorPolynomial (X ⊕ (Σ j, J j)) R V :=
  (MvPolynomial.rename (R := R) (lowTaggedVariableEmbedding (X := X) J k)).toLinearMap.rTensor V

@[simp] theorem lowTaggedVectorRestrict_tmul (k : ℕ)
    (P : MvPolynomial (X ⊕ (Σ j, J j)) R) (v : V) :
    lowTaggedVectorRestrict J k (P ⊗ₜ[R] v) = lowTaggedRestrict J k P ⊗ₜ[R] v := rfl

@[simp] theorem lowTaggedVectorExtend_tmul (k : ℕ)
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R) (v : V) :
    lowTaggedVectorExtend J k (P ⊗ₜ[R] v) =
      MvPolynomial.rename (lowTaggedVariableEmbedding J k) P ⊗ₜ[R] v := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]
    {X R S V : Type*} [CommRing R] [CommRing S]
    [AddCommGroup V] [Module R V]

@[simp] theorem lowTaggedVectorExtend_monomial (k : ℕ)
    (α : (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) →₀ ℕ) (v : V) :
    lowTaggedVectorExtend J k (monomial (R := R) α v) =
      monomial (α.mapDomain (lowTaggedVariableEmbedding J k)) v := by
  rw [monomial, lowTaggedVectorExtend_tmul, MvPolynomial.rename_monomial]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {X κ : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

def fullTaggedGradedBaseIntersection (k : ℕ)
    (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
    (K : κ → Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)) :
    Set (X ⊕ (Σ j, J j) → ℝ) :=
  {t | t ∈ K₀ ∧ ∀ i, (fun b => t (lowTaggedVariableEmbedding J k (Sum.inr b))) ∈ K i}

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FullTaggedChartCoefficientRange
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def fullTaggedMajorTopCoordinates
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (a : Σ j, J j) : MvPolynomial X ℝ :=
  homogeneousComponent (a.1.val + 1)
    (coordinate (LinearMap.proj a.2 : (J a.1 → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom (poly a.1))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FullChartHomogeneousCorrection
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {m : ℕ} {X : Type} {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}

structure FullChartFiniteHistory
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
    (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
    (Utag : ∀ j, Submodule ℝ (J j → ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (N : X → ℕ) (Bphase : ℝ) (n : ℕ) where
  slow : ℕ → VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
  rat : ℕ → VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
  q : ℕ → ℕ
  K : Set (X ⊕ (Σ j, J j) → ℝ)
  subset : K ⊆ Kinitial
  dilation : ∀ t ∈ K, ∀ r : ℚ,
    (fun i => (r : ℝ) ^ fullTaggedVariableWeight J i * t i) ∈ K
  retained : ∀ t ∈ Kinitial, (∀ j, (fun a => t (Sum.inr ⟨j, a⟩)) ∈ Utag j) → t ∈ K
  slow_bound : ∀ j < n, ∀ α i, |basis.coord i (coefficients (slow j) α)| ≤ Real.exp Bphase
  q_pos : ∀ j < n, 0 < q j
  q_bound : ∀ j < n, (q j : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * Bphase)
  rat_grid : ∀ j < n, ∀ α,
    (fun i => basis.coord i (coefficients (rat j) α)) ∈ realDenominatorGrid (q j)
  invariant :
    let outer := F.restrictedMajorOuterFactors b ω hF (fullTaggedVariableWeight J) fast lift
      (fun j => realChartSubstitute (normalizedRealPolynomialChart (fun i => (N i : ℝ))
        (fullTaggedMajorTopCoordinates J poly)) (slow j)) rat n
    ∀ t ∈ K, ∀ j ≤ n,
      F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) j t
        (outer.1⁻¹ * Z * outer.2⁻¹).coord ∈ fast.baseChange ℝ

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartDecompositionSource
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

def FullChartMajorCorrelation
    {m : ℕ} {X L M ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (D : RationalFilteredNilmanifold M t e)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (p Rrank : ℝ) (C : ℕ) : Prop :=
  ∃ (periodCap coverCap : ℝ) (Lip : ℝ≥0)
    (W : η → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (R : η → D.Niltest (fun _ : X => 1))
    (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J k)))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J k)) → ℤ),
    (∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j)) ∧
    (∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j) ∧
    (∀ u ∈ integerBox N, ∀ i,
      |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly i) -
        c i - (β u i : ℝ)| ≤ 1 / 2) ∧
    0 ≤ p ∧ (∀ j, (R j).ComplexityLE p) ∧
    (∀ j, ((R j).normBound : ℝ) ≤ 1) ∧
    ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ p ∧
    (∀ j, ((W j).modulus : ℝ) ≤ Real.exp p) ∧
    (∀ j, ((W j).cover : ℝ) ≤ Real.exp p) ∧
    (Lip : ℝ) ≤ Real.exp p ∧ (Ψ.lip : ℝ) ≤ Real.exp p ∧
    (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) ∧
    Real.exp ((p + C) ^ C) ≤ Rrank ∧
    (∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)) ∧
    (∀ j, Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
      (W j).eval N poly u * majorPhaseSample J k poly Ψ c
        (coordinate (basis.coord j).toAddMonoidHom
          (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
            (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord))) β (R j).eval u‖)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

def FullChartControlledFactors
    {m : ℕ} {X L ι : Type} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (budget : ℝ) : Prop :=
  ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
    ∃ Echart : PolynomialGroup (X ⊕ (Σ j, J j))
        F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot,
      F.realGradedSymbolPolynomialHom b ω hF (fullTaggedVariableWeight (X := X) J) left =
        realPolynomialChartSubstitution
          F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot
          (normalizedRealPolynomialChart (fun i => (N i : ℝ))
            (fullTaggedMajorTopCoordinates J poly)) Echart ∧
      CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) (fun _ => 1)
        (Real.exp budget) Echart.coord ∧
      CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) q
        (F.realGradedSymbolPolynomialHom b ω hF
          (fullTaggedVariableWeight (X := X) J) right).coord

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

structure FullChartMajorCorrelationWitness
    {m : ℕ} {X L ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (p Rrank : ℝ) (C : ℕ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  step : ℕ
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L step dim
  lower : step < k
  correlation : FullChartMajorCorrelation F b ω hF J k fast basis
    Z left right model N poly U p Rrank C

attribute [local instance] FullChartMajorCorrelationWitness.lie
  FullChartMajorCorrelationWitness.algebra FullChartMajorCorrelationWitness.topology
  FullChartMajorCorrelationWitness.topologicalAdd FullChartMajorCorrelationWitness.continuousSMul
  FullChartMajorCorrelationWitness.hausdorff

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoundedCertifiedFullChartMajorIteration
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {m : ℕ} {X : Type} {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}

structure CertifiedFullChartFiniteHistory
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
    (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
    (Utag : ∀ j, Submodule ℝ (J j → ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (N : X → ℕ) (Bphase : ℝ) (n : ℕ) where
  slow : ℕ → VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
  rat : ℕ → VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
  q : ℕ → ℕ
  K : Set (X ⊕ (Σ j, J j) → ℝ)
  certificate : RationalTaggedConstraintCertificate J Kinitial K Bphase
    (n * (Fintype.card η * m))
  subset : K ⊆ Kinitial
  dilation : ∀ t ∈ K, ∀ r : ℚ,
    (fun i => (r : ℝ) ^ fullTaggedVariableWeight J i * t i) ∈ K
  retained : ∀ t ∈ Kinitial, (∀ j, (fun a => t (Sum.inr ⟨j, a⟩)) ∈ Utag j) → t ∈ K
  slow_bound : ∀ j < n, ∀ α i, |basis.coord i (coefficients (slow j) α)| ≤ Real.exp Bphase
  q_pos : ∀ j < n, 0 < q j
  q_bound : ∀ j < n, (q j : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * Bphase)
  rat_grid : ∀ j < n, ∀ α,
    (fun i => basis.coord i (coefficients (rat j) α)) ∈ realDenominatorGrid (q j)
  invariant :
    let outer := F.restrictedMajorOuterFactors b ω hF (fullTaggedVariableWeight J) fast lift
      (fun j => realChartSubstitute (normalizedRealPolynomialChart (fun i => (N i : ℝ))
        (fullTaggedMajorTopCoordinates J poly)) (slow j)) rat n
    ∀ t ∈ K, ∀ j ≤ n,
      F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) j t
        (outer.1⁻¹ * Z * outer.2⁻¹).coord ∈ fast.baseChange ℝ

namespace CertifiedFullChartFiniteHistory

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)]
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (Bphase : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)
local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase

noncomputable def outer {n : ℕ} (H : State n) :
    F.RealPolynomialSymbolGroup wt × F.RealPolynomialSymbolGroup wt :=
  F.restrictedMajorOuterFactors b ω hF wt fast lift
    (fun j => realChartSubstitute chart (H.slow j)) H.rat n

end CertifiedFullChartFiniteHistory
end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.InhomogeneousFullChartLift
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def gradedPolynomialProjection (w : σ → ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) :
    VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded) :=
  F.realGradedSymbolPolynomial b ω hF w (F.realSymbolOfGradedPolynomial b ω hF w P)

attribute [local irreducible] realChartSubstitute realGradedSymbolPolynomial
  realSymbolOfGradedPolynomial realSymbolHomogeneousPullback gradedPolynomialProjection

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TerminalChartSlowEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {m : ℕ} {X : Type}
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (budget : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "quotientReal" => ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

def FullChartAdmissibleStageCorrection
    (q : ℕ) (K' : Set (X ⊕ (Σ j, J j) → ℝ))
    (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal ×
      VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal) : Prop :=
      (∀ α, Finsupp.weight wt α ≠ k → coefficients pair.1 α = 0) ∧
      (∀ α, Finsupp.weight wt α ≠ k → coefficients pair.2 α = 0) ∧
      (∀ i, (coordinate (basis.coord i).toAddMonoidHom pair.1).totalDegree ≤ k) ∧
      (∀ i, (coordinate (basis.coord i).toAddMonoidHom pair.2).totalDegree ≤ k) ∧
      0 < q ∧ (q : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * budget) ∧
      K' ⊆ K₀ ∧
      (∀ t ∈ K', ∀ r : ℚ, (fun i => (r : ℝ) ^ wt i * t i) ∈ K') ∧
      (∀ t ∈ K₀, (∀ j, (fun a => t (Sum.inr ⟨j, a⟩)) ∈ Utag j) → t ∈ K') ∧
      (∀ α i, |basis.coord i (coefficients pair.1 α)| ≤ Real.exp budget) ∧
      (∀ α, (fun i => basis.coord i (coefficients pair.2 α)) ∈ realDenominatorGrid q) ∧
      (∀ t ∈ K', ∀ j ≤ k,
        F.realSymbolGradeEvaluation b ω hF wt j t
          ((left * F.restrictedMajorCorrection b ω hF wt fast lift k
              (realChartSubstitute chart pair.1))⁻¹ * Z *
            (F.restrictedMajorCorrection b ω hF wt fast lift k pair.2 * right)⁻¹).coord ∈
          fast.baseChange ℝ) ∧
      (∃ (detectedfast : η → LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J k) k))
        (slow rat : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℚ quotientReal),
        pair.1 = lowTaggedVectorExtend J k slow ∧ pair.2 = lowTaggedVectorExtend J k rat ∧
        K' = fullTaggedGradedBaseIntersection J k K₀
          (fun i => majorPhaseDetectedRealBase J k (detectedfast i))) ∧
      RationalTaggedConstraintCertificate J K₀ K' budget (Fintype.card η * m) ∧
      ∀ t ∈ K', eval₂ t
        (F.realSymbolGradeQuotientPolynomial b ω hF wt fast k (left⁻¹ * Z * right⁻¹).coord) =
        eval₂ t (realChartSubstitute chart pair.1) + eval₂ t pair.2

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] realSymbolGradeEvaluation restrictedMajorCorrection
  realSymbolGradeQuotientPolynomial outer

variable {m : ℕ} {X : Type} {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)]
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (Bphase : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)
local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase

variable {F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase}

theorem exists_append_admissible {n : ℕ} (H : State n)
    (budget : ℝ) (hbudget : budget ≤ Bphase) (q : ℕ)
    (K' : Set (X ⊕ (Σ j, J j) → ℝ))
    (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
      VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) :
    ∃ Hnext : State (n + 1),
      Hnext.slow = Function.update H.slow n pair.1 ∧
      Hnext.rat = Function.update H.rat n pair.2 ∧
      Hnext.q = Function.update H.q n q ∧ Hnext.K = K' := by
  let pS := pair.1
  let pR := pair.2
  have hq := hpair.2.2.2.2.1
  have hqB := hpair.2.2.2.2.2.1
  have hsub := hpair.2.2.2.2.2.2.1
  have hdilate := hpair.2.2.2.2.2.2.2.1
  have hretain := hpair.2.2.2.2.2.2.2.2.1
  have hcap := hpair.2.2.2.2.2.2.2.2.2.1
  have hgrid := hpair.2.2.2.2.2.2.2.2.2.2.1
  have hnext := hpair.2.2.2.2.2.2.2.2.2.2.2.1
  have hcert := hpair.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  let slow' := Function.update H.slow n pS
  let rat' := Function.update H.rat n pR
  let q' := Function.update H.q n q
  have hslow (j : ℕ) (hj : j < n) : slow' j = H.slow j :=
    Function.update_of_ne (Nat.ne_of_lt hj) _ _
  have hrat (j : ℕ) (hj : j < n) : rat' j = H.rat j :=
    Function.update_of_ne (Nat.ne_of_lt hj) _ _
  have hqold (j : ℕ) (hj : j < n) : q' j = H.q j :=
    Function.update_of_ne (Nat.ne_of_lt hj) _ _
  have hprefix : F.restrictedMajorOuterFactors b ω hF wt fast lift
      (fun j => realChartSubstitute chart (slow' j)) rat' n = H.outer := by
    unfold outer
    apply F.restrictedMajorOuterFactors_congr
    · intro j hj
      rw [hslow j hj]
    · exact hrat
  have houter : F.restrictedMajorOuterFactors b ω hF wt fast lift
      (fun j => realChartSubstitute chart (slow' j)) rat' (n + 1) =
      (H.outer.1 * F.restrictedMajorCorrection b ω hF wt fast lift (n + 1)
        (realChartSubstitute chart pS),
       F.restrictedMajorCorrection b ω hF wt fast lift (n + 1) pR * H.outer.2) := by
    rw [restrictedMajorOuterFactors, hprefix]
    simp only [slow', rat', Function.update_self]
  have hcapB : ∀ α i, |basis.coord i (coefficients pS α)| ≤ Real.exp Bphase :=
    fun α i => (hcap α i).trans (Real.exp_le_exp.mpr hbudget)
  have hqBB : (q : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * Bphase) :=
    hqB.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg _)))
  let Hnext : State (n + 1) := {
    slow := slow'
    rat := rat'
    q := q'
    K := K'
    certificate := by
      simpa only [Nat.succ_mul] using H.certificate.trans (hcert.monoB hbudget)
    subset := fun t ht => H.subset (hsub ht)
    dilation := hdilate
    retained := fun t ht hU => hretain t (H.retained t ht hU) hU
    slow_bound := by
      intro j hj α i
      by_cases hjn : j = n
      · subst j
        simpa only [slow', Function.update_self] using hcapB α i
      · rw [hslow j (by omega)]
        exact H.slow_bound j (by omega) α i
    q_pos := by
      intro j hj
      by_cases hjn : j = n
      · subst j
        simpa only [q', Function.update_self] using hq
      · rw [hqold j (by omega)]
        exact H.q_pos j (by omega)
    q_bound := by
      intro j hj
      by_cases hjn : j = n
      · subst j
        simpa only [q', Function.update_self] using hqBB
      · rw [hqold j (by omega)]
        exact H.q_bound j (by omega)
    rat_grid := by
      intro j hj α
      by_cases hjn : j = n
      · subst j
        simpa only [rat', q', Function.update_self] using hgrid α
      · rw [hrat j (by omega), hqold j (by omega)]
        exact H.rat_grid j (by omega) α
    invariant := by
      dsimp only
      rw [houter]
      with_reducible exact hnext }
  exact ⟨Hnext, rfl, rfl, rfl, rfl⟩

noncomputable def append_admissible {n : ℕ} (H : State n) (budget : ℝ) (hbudget : budget ≤ Bphase) (q : ℕ)
  (K' : Set (X ⊕ (Σ j, J j) → ℝ))
  (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
    VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) : State (n + 1) :=
  Classical.choose (exists_append_admissible H budget hbudget q K' pair hpair)

@[simp] theorem append_admissible_slow
    {n : ℕ} (H : State n) (budget : ℝ) (hbudget : budget ≤ Bphase) (q : ℕ)
  (K' : Set (X ⊕ (Σ j, J j) → ℝ))
  (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
    VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) :
    (H.append_admissible budget hbudget q K' pair hpair).slow =
      Function.update H.slow n pair.1 :=
  (Classical.choose_spec (exists_append_admissible H budget hbudget q K' pair hpair)).1

@[simp] theorem append_admissible_rat
    {n : ℕ} (H : State n) (budget : ℝ) (hbudget : budget ≤ Bphase) (q : ℕ)
  (K' : Set (X ⊕ (Σ j, J j) → ℝ))
  (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
    VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) :
    (H.append_admissible budget hbudget q K' pair hpair).rat =
      Function.update H.rat n pair.2 :=
  (Classical.choose_spec (exists_append_admissible H budget hbudget q K' pair hpair)).2.1

@[simp] theorem append_admissible_q
    {n : ℕ} (H : State n) (budget : ℝ) (hbudget : budget ≤ Bphase) (q : ℕ)
  (K' : Set (X ⊕ (Σ j, J j) → ℝ))
  (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
    VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) :
    (H.append_admissible budget hbudget q K' pair hpair).q =
      Function.update H.q n q :=
  (Classical.choose_spec (exists_append_admissible H budget hbudget q K' pair hpair)).2.2.1

@[simp] theorem append_admissible_entry
    {n : ℕ} (H : State n) (budget : ℝ) (hbudget : budget ≤ Bphase) (q : ℕ)
  (K' : Set (X ⊕ (Σ j, J j) → ℝ))
  (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
    VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) :
    (H.append_admissible budget hbudget q K' pair hpair).slow n = pair.1 ∧
    (H.append_admissible budget hbudget q K' pair hpair).rat n = pair.2 ∧
    (H.append_admissible budget hbudget q K' pair hpair).q n = q := by
  simp only [CertifiedFullChartFiniteHistory.append_admissible_slow,
    CertifiedFullChartFiniteHistory.append_admissible_rat, CertifiedFullChartFiniteHistory.append_admissible_q,
    Function.update_self, and_self]

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualForecastDataNativeProductBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

structure ActualForecastData (N : X → ℕ)
    (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (Pnative massLog capLog E : ℝ) where
  target : integerBox N → ℂ
  centerConstant : ∀ j, J j → ℝ
  Term : Type
  [fintypeTerm : Fintype Term]
  coefficient : Term → ℂ
  twists : Term → NormalizedPolynomialTwist X (Σ j, J j)
    (Real.exp (3 * Pnative + 3)) (Real.exp (3 * Pnative + 3))
    ⟨Real.exp (3 * Pnative + 3), Real.exp_nonneg _⟩
  cap : ∀ v, ‖target v‖ ≤ Real.exp capLog
  mass : (∑ i, ‖coefficient i‖) ≤ Real.exp massLog
  approximation : ∀ v, ‖target v - ∑ i, coefficient i *
    (twists i).eval N (fun j => subtractConstant (centerConstant j) (originalpoly j)) v.val‖ ≤
      Real.exp (-E)

attribute [instance] ActualForecastData.fintypeTerm

namespace ActualForecastData

variable (N : X → ℕ) (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (Pnative massLog capLog E : ℝ)

noncomputable def zero : ActualForecastData N originalpoly Pnative massLog capLog E where
  target := fun _ => 0
  centerConstant := fun _ _ => 0
  Term := Empty
  coefficient := fun i => nomatch i
  twists := fun i => nomatch i
  cap := fun _ => by simpa only [norm_zero] using Real.exp_nonneg capLog
  mass := by simpa using Real.exp_nonneg massLog
  approximation := fun _ => by simpa using Real.exp_nonneg (-E)

@[simp] theorem zero_target (v : integerBox N) :
    (zero N originalpoly Pnative massLog capLog E).target v = 0 := rfl

@[simp] theorem zero_centerConstant (j : Fin m) (i : J j) :
    (zero N originalpoly Pnative massLog capLog E).centerConstant j i = 0 := rfl

end ActualForecastData

variable {N : X → ℕ} {originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
variable {Pnative massLog capLog E : ℝ} {F : Type*}

noncomputable def actualForecastOptionFamily
    (data : F → ActualForecastData N originalpoly Pnative massLog capLog E) :
    Option F → ActualForecastData N originalpoly Pnative massLog capLog E
  | none => ActualForecastData.zero N originalpoly Pnative massLog capLog E
  | some f => data f

@[simp] theorem actualForecastOptionFamily_some
    (data : F → ActualForecastData N originalpoly Pnative massLog capLog E) (f : F) :
    actualForecastOptionFamily data (some f) = data f := rfl

@[simp] theorem actualForecastOptionFamily_none_target
    (data : F → ActualForecastData N originalpoly Pnative massLog capLog E)
    (v : integerBox N) : (actualForecastOptionFamily data none).target v = 0 := rfl

@[simp] theorem actualForecastOptionFamily_none_centerConstant
    (data : F → ActualForecastData N originalpoly Pnative massLog capLog E)
    (j : Fin m) (i : J j) :
    (actualForecastOptionFamily data none).centerConstant j i = 0 := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankBadProduct
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)

def allocatedCongruenceRankBad (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ) :
    ℕ → ℕ → (AllocatedCongruenceScalarIndex X E inactive L → ℤ) → Prop :=
  smoothResiduePrimeBad P (fun p a =>
    allocatedCongruenceModulusBad inactive noise r projection spatial kernel block C (p.val ^ a))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRecoveredPreparedFreeze
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (C : ℝ)
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

def AllocatedCenteredFramedRecoveredSampleAt
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (s : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) : Prop :=
  allocatedReadNoise f = (fun t => jointIntegerFrame (a,v) t.1 t.2) ∧
  canonicalCoefficientSample U b hb o s =
    affineSampleCoefficientTorus U (fun j => subtractConstant (c j).val (poly j))
      (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hm j))
      (fun k x => (jointIntegerFrame (a,v) k x : ℝ)) ∧
  (∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (s j) ∧
    mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (s j)) ∧
  (∀ d, |coefficientSamplerAmbientPoint U b o s d| < 1/2) ∧
  (∀ (j : Fin m) (i : Fin (n j))
    (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
    allocatedReadProjection f ⟨j, Sum.inr i⟩ e = (s j).2 i e)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedRecoveredIntegerFullChart
namespace OAI

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel _root_.MvPolynomial
open scoped BigOperators
variable {m : ℕ} {K X : Type*} [Fintype K] (J : Fin m → Type*)
    (a : X → ℤ) (v : Option K × X → ℤ)
    (tag : ∀ j, J j → MvPolynomial K ℤ)

theorem jointIntegerFullChart_support
    (htag : ∀ j b, (tag j b).totalDegree ≤ j.val + 1) :
    ∀ i, integerSampledRealChart (jointIntegerFullChart J a v tag) i ∈
      weightedSupportLE (fun _ : K => 1) (fullTaggedVariableWeight J i) := by
  intro i
  apply (mem_weightedSupportLE_one_iff _ _).mpr
  cases i with
  | inl x =>
    change (MvPolynomial.map (Int.castRingHom ℝ)
      (affineFramePolynomial (jointIntegerFrame (a, v)) x)).totalDegree ≤ 1
    exact (totalDegree_map_le _ _).trans (affineFramePolynomial_degree _ _)
  | inr z =>
    change (MvPolynomial.map (Int.castRingHom ℝ) (tag z.1 z.2)).totalDegree ≤ z.1.val + 1
    exact (totalDegree_map_le _ _).trans (htag z.1 z.2)

end Erdos3.VectorPolynomial

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

noncomputable def allocatedRecoveredIntegerFullChart
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n) :
    X ⊕ (Σ j, J j) → MvPolynomial (LayerSamplerVariables G I n B) ℤ :=
  jointIntegerFullChart J a v
    (coefficientIntegerFloorPolynomial U b o sample
      (centeredAffineCoefficientArray U poly hm c
        (fun k z => (jointIntegerFrame (a, v) k z : ℝ))))

theorem allocatedRecoveredIntegerFullChart_support
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n) :
    ∀ i, integerSampledRealChart (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) i ∈
      weightedSupportLE (fun _ : LayerSamplerVariables G I n B => 1) (fullTaggedVariableWeight J i) := by
  apply jointIntegerFullChart_support
  exact coefficientIntegerFloorPolynomial_degree U b o sample _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerFrozenChart
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial
open scoped Classical

variable {I R : Type*} [CommRing R]

theorem freezePolynomial_support (keep : I → Prop) (fixed : {i // ¬keep i} → R)
    {P : MvPolynomial I R} {d : ℕ} (hP : P ∈ weightedSupportLE (fun _ => 1) d) :
    freezePolynomial keep fixed P ∈ weightedSupportLE (fun _ => 1) d :=
  weightedSupportLE_aeval (fun _ => 1) (fun _ => 1) _ (frozenCoordinate_support keep fixed) hP

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartFrozenTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

theorem allocatedFrozenParameterBox_mem
    (keep : LayerSamplerVariables G I n B → Prop) [DecidablePred keep]
    (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < sides i.val)
    (u : {i // keep i} → ℤ)
    (hu : u ∈ integerBox (fun i : {i // keep i} => sides i.val)) :
    finiteSplitPoint keep u fixed ∈ integerBox sides := by
  apply (mem_integerBox sides _).mpr
  intro i
  by_cases hi : keep i
  · simpa only [finiteSplitPoint, dif_pos hi] using
      (mem_integerBox _ u).mp hu ⟨i, hi⟩
  · simpa only [finiteSplitPoint, dif_neg hi] using hfixed ⟨i, hi⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule _root_.MvPolynomial BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

noncomputable def allocatedFrozenIntegerFullChart
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ) :
    X ⊕ (Σ j, J j) → MvPolynomial {i // keep i} ℤ :=
  fun z => freezePolynomial keep fixed
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)

theorem allocatedFrozenIntegerFullChart_support
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ) :
    ∀ i, integerSampledRealChart
      (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed) i ∈
      weightedSupportLE (fun _ : {i // keep i} => 1) (fullTaggedVariableWeight J i) := by
  intro i
  change integerSampledRealChart (fun z => freezePolynomial keep fixed
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)) i ∈ _
  rw [integerSampledRealChart_freeze]
  exact freezePolynomial_support keep _
    (allocatedRecoveredIntegerFullChart_support B U b o poly hm c a v sample i)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoordinateFreezeBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

attribute [local irreducible] weightedAdaptedRealChartHom realChartSubstitute

noncomputable def polynomialCoordinateFreezeZeroHom (keep : σ → Prop) :
    (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group →*
      (F.realification.adaptedPolynomialFiltration (fun _ : {i // keep i} => 1)).Group :=
  F.weightedAdaptedRealChartHom (fun _ : σ => 1) (fun _ : {i // keep i} => 1)
    (frozenCoordinate keep (0 : {i // ¬keep i} → ℝ))
    (frozenCoordinate_support keep 0)

@[simp] theorem polynomialCoordinateFreezeZeroHom_coord (keep : σ → Prop)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) :
    ((F.polynomialCoordinateFreezeZeroHom keep g).coord :
        VectorPolynomial {i // keep i} ℚ (ℝ ⊗[ℚ] L)) =
      realChartSubstitute (frozenCoordinate keep 0)
        (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := by
  exact F.weightedAdaptedRealChartHom_coord _ _ _ _ g

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeIntegerChartNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

attribute [local irreducible] realChartSubstitute polynomialOrbitRealChart
  weightedAdaptedRealChartHom realPolynomialSymbolHom

variable {L σ τ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  (Q : D.Niltest w) (v : τ → ℕ) (β : σ → MvPolynomial τ ℤ)
  (hβ : ∀ i, integerSampledRealChart β i ∈ weightedSupportLE v (w i))

noncomputable def integerChartPullback : D.Niltest v :=
  Q.withOrbit (D.filtration.polynomialOrbitRealChart w v (integerSampledRealChart β) hβ Q.orbit)

@[simp] theorem integerChartPullback_orbit :
    (Q.integerChartPullback v β hβ).orbit =
      D.filtration.polynomialOrbitRealChart w v (integerSampledRealChart β) hβ Q.orbit := rfl

@[simp] theorem integerChartPullback_observable :
    (Q.integerChartPullback v β hβ).observable = Q.observable := rfl

@[simp] theorem integerChartPullback_normBound :
    (Q.integerChartPullback v β hβ).normBound = Q.normBound := rfl

@[simp] theorem integerChartPullback_lipBound :
    (Q.integerChartPullback v β hβ).lipBound = Q.lipBound := rfl

@[simp] theorem integerChartPullback_complexity (p : ℝ) :
    (Q.integerChartPullback v β hβ).ComplexityLE p ↔ Q.ComplexityLE p := Iff.rfl

@[simp] theorem integerChartPullback_unitIntervalValued :
    (Q.integerChartPullback v β hβ).UnitIntervalValued ↔ Q.UnitIntervalValued := Iff.rfl

@[simp] theorem integerChartPullback_eval (t : τ → ℤ) :
    (Q.integerChartPullback v β hβ).eval t =
      Q.eval (fun i => MvPolynomial.eval t (β i)) := by
  change Q.observable (QuotientGroup.mk
    (D.filtration.realification.polynomialOrbitEval v t
      (D.filtration.polynomialOrbitRealChart w v (integerSampledRealChart β) hβ Q.orbit))) = _
  rw [← D.filtration.realification.polynomialOrbitRealEval_integer,
    D.filtration.polynomialOrbitRealChart_realEval]
  simp only [integerSampledRealChart_eval]
  rw [D.filtration.realification.polynomialOrbitRealEval_integer]
  rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateOptionJointConclusion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

structure AllocatedExternalLocalChart (cost : ℝ) where
  path : A.Path
  path_supported : 0 < A.law.weight path
  centerLift : ∀ j, U j
  center_eq : coefficientConstantCenter U center =
    -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
      (constantCoefficientArray U (fun s => centerLift s.1)))
  sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
  read : AllocatedActualCoefficientIndex G X I E n B → ℤ
  recovered : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
    centerLift path.1.val path.2.val sample read
  keep : LayerSamplerVariables G I n B → Prop
  fixed : {i // ¬keep i} → ℤ
  fixed_in_box : ∀ i, 0 ≤ fixed i ∧ fixed i < A.sides i.val
  step : ℕ
  step_pos : 0 < step
  slice : ResidueBoxSlice (fun i : {i // keep i} => A.sides i.val) step
  dense : IsDenseCommonStrideBox (fun i : {i // keep i} => A.sides i.val) cost slice.integerPoints

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

abbrev Variables := {i // C.keep i}

noncomputable def integerChart : X ⊕ (Σ j, J j) → MvPolynomial C.Variables ℤ :=
  allocatedFrozenIntegerFullChart B U b o poly hm C.centerLift C.path.1.val C.path.2.val
    C.sample C.keep C.fixed

noncomputable def chartValues (u : C.Variables → ℤ) : X ⊕ (Σ j, J j) → ℤ :=
  fun i => MvPolynomial.eval u (C.integerChart i)

noncomputable def parameter (u : C.Variables → ℤ) : LayerSamplerVariables G I n B → ℤ :=
  finiteSplitPoint C.keep u C.fixed

theorem parameter_mem (u : C.Variables → ℤ)
    (hu : u ∈ integerBox (fun i : C.Variables => A.sides i.val)) :
    C.parameter u ∈ integerBox A.sides :=
  allocatedFrozenParameterBox_mem B U b S C.keep C.fixed C.fixed_in_box u hu

noncomputable def physical (u : C.Variables → ℤ) : X → ℤ :=
  jointIntegerPhysicalSite (C.parameter u) (C.path.1.val, C.path.2.val)

noncomputable def site (u : C.Variables → ℤ)
    (hu : u ∈ integerBox (fun i : C.Variables => A.sides i.val)) : A.Site :=
  ⟨C.parameter u, C.parameter_mem u hu⟩

@[simp] theorem physical_eq_sampler (u : C.Variables → ℤ)
    (hu : u ∈ integerBox (fun i : C.Variables => A.sides i.val)) :
    C.physical u = A.physical C.path (C.site u hu) := rfl

end AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (Fmark : NilpotentLieFiltration M t) (φ : L →ₗ⁅ℚ⁆ M)
    (marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))

structure AllocatedExternalLocalCandidate where
  orbit : D.filtration.realification.PolynomialOrbit (fun _ : C.Variables => 1)
  mark_on_slice : ∀ u ∈ C.slice.integerPoints,
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fun _ : C.Variables => 1) u orbit) =
    Fmark.realification.polynomialOrbitEval (fullTaggedVariableWeight J) (C.chartValues u) marked

namespace AllocatedExternalLocalCandidate

variable {C D Fmark φ marked}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)

noncomputable def value (u : C.Variables → ℤ) : D.Space :=
  QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
    (fun _ : C.Variables => 1) u candidate.orbit)

noncomputable def score (observable : (X → ℤ) → D.Space → ℂ)
    (weight : (X → ℤ) → ℂ) : ℝ :=
  (𝔼 u ∈ C.slice.integerPoints, weight (C.physical u) *
    observable (C.physical u) (candidate.value u)).re

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    (D : RationalFilteredNilmanifold L r d) (Fmark : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M)
    (marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)

structure AllocatedExternalCandidateProblem (cost massThreshold scoreThreshold : ℝ) where
  productive : Finset A.Path
  mass : massThreshold ≤ A.law.mass productive
  chart : ∀ _z : productive, AllocatedExternalLocalChart (E := E) A cost
  chart_path : ∀ z, (chart z).path = z.val
  centerLift : ∀ j, U j
  chart_centerLift : ∀ z, (chart z).centerLift = centerLift
  frozen_side : ∀ z (i : {i // ¬(chart z).keep i}), (A.sides i.val : ℝ) ≤ Real.exp cost
  candidate : ∀ z, AllocatedExternalLocalCandidate (chart z) D Fmark φ marked
  score : ∀ z, scoreThreshold ≤ (candidate z).score observable weight

namespace AllocatedExternalCandidateProblem
variable {A D Fmark φ marked observable weight cost massThreshold scoreThreshold}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

noncomputable def ambientScore
    (ambient : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (z : P.productive) (points : Finset ((P.chart z).Variables → ℤ)) : ℝ :=
  (𝔼 u ∈ points, weight ((P.chart z).physical u) *
    observable ((P.chart z).physical u) (QuotientGroup.mk
      (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
        ((P.chart z).chartValues u) ambient))).re

end AllocatedExternalCandidateProblem

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductiveFrozenLocalMajorFamily
namespace OAI

section

namespace Erdos3
open scoped TensorProduct BigOperators
variable {I L : Type*} [Fintype I] [DecidableEq I]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

structure LocalMajorSliceTest (D : RationalFilteredNilmanifold L s d)
    (N : I → ℕ) (cost budget : ℝ) where
  stride : ℕ
  stride_pos : 0 < stride
  slice : ResidueBoxSlice N stride
  dense : IsDenseCommonStrideBox N cost slice.integerPoints
  test : D.Niltest (fun _ : I => 1)
  norm : (test.normBound : ℝ) ≤ 1
  complexity : test.ComplexityLE budget

namespace LocalMajorSliceTest
variable {D : RationalFilteredNilmanifold L s d} {N : I → ℕ} {cost budget : ℝ}
noncomputable def weight (A : LocalMajorSliceTest D N cost budget) (x : I → ℤ) : ℂ :=
  star (A.test.eval (commonStrideIndex (fun i => (A.slice.start i : ℤ)) A.stride x))
end LocalMajorSliceTest

end Erdos3

end

section

namespace Erdos3.LocalMajorSliceTest
open scoped TensorProduct

variable {I L : Type*} [Fintype I] [DecidableEq I]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {N : I → ℕ}
    {cost budget cost' budget' : ℝ}

def mono (packet : LocalMajorSliceTest D N cost budget)
    (hcost : cost ≤ cost') (hbudget : budget ≤ budget') :
    LocalMajorSliceTest D N cost' budget' where
  stride := packet.stride
  stride_pos := packet.stride_pos
  slice := packet.slice
  dense := packet.dense.mono hcost
  test := packet.test
  norm := packet.norm
  complexity := packet.complexity.mono hbudget

@[simp] theorem mono_weight (packet : LocalMajorSliceTest D N cost budget)
    (hcost : cost ≤ cost') (hbudget : budget ≤ budget') (x : I → ℤ) :
    (packet.mono hcost hbudget).weight x = packet.weight x := rfl

end Erdos3.LocalMajorSliceTest

end

section

namespace Erdos3
open scoped TensorProduct BigOperators

variable {I : Type} [Fintype I] [DecidableEq I]

namespace UniversalLocalMajorSliceTest

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

variable {N : I → ℕ} {degree : ℕ} {cost budget : ℝ}

noncomputable def ofLocalMajorSliceTest
    {L : Type} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L degree d}
    (packet : LocalMajorSliceTest D N cost budget) :
    UniversalLocalMajorSliceTest N degree cost budget where
  stride := packet.stride
  stride_pos := packet.stride_pos
  slice := packet.slice
  dense := packet.dense
  value := packet.test.eval
  native := ⟨{
    L := L
    dim := d
    model := D
    test := packet.test
    norm := by exact_mod_cast packet.norm
    complexity := packet.complexity
    eval := fun _ => rfl }⟩

@[simp] theorem ofLocalMajorSliceTest_weight
    {L : Type} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L degree d}
    (packet : LocalMajorSliceTest D N cost budget) (x : I → ℤ) :
    (ofLocalMajorSliceTest packet).weight x = packet.weight x := rfl

@[simp] theorem ofLocalMajorSliceTest_slice
    {L : Type} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L degree d}
    (packet : LocalMajorSliceTest D N cost budget) :
    (ofLocalMajorSliceTest packet).slice = packet.slice := rfl

end UniversalLocalMajorSliceTest
end Erdos3

end

end OAI
end


