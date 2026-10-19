-- Prove2me | Definitions.Def_OAIE3v2B085
-- name    : OAIE3v2B085
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:21:27.426456+00:00
-- url     : https://prove2.me/theorems/09bfc740-609a-4088-b923-7af068903cbb
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 86 of 311
-- statement:
--   Definitions bundle 86 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B038`, `OAIE3v2B039`, `OAIE3v2B040`, `OAIE3v2B044`, `OAIE3v2B045`, `OAIE3v2B046`, `OAIE3v2B047`, `OAIE3v2B048`, `OAIE3v2B049`, `OAIE3v2B056`, `OAIE3v2B058`, `OAIE3v2B059`, `OAIE3v2B060`, `OAIE3v2B061`, `OAIE3v2B063`, `OAIE3v2B064`, `OAIE3v2B065`, `OAIE3v2B066`, `OAIE3v2B067` of this split.
--
--   Modules: `Dynamics/CandidateCommonFastBudgetMonotonicity.lean`, `Dynamics/CandidateFrontActualPowerBudget.lean`, `Dynamics/FixedListPowerBudget.lean`, `Dynamics/PositiveModerateBudget.lean`, `Dynamics/PreparedFinalScalarPowerBudget.lean`, `Dynamics/PreparedModularCanonicalDetectorResourceBudget.lean`, `Dynamics/PreparedRelativeEndpointComparisonBudget.lean`, `Dynamics/ScalarCubeBoundaryLogBudget.lean`, `Estimates/AllocatedCenteredJointSource.lean`, `Estimates/AllocatedExternalCandidateTaggedPairUniformFactors.lean`, `Estimates/AllocatedFiniteModelPhysicalExpansion.lean`, `Estimates/AllocatedSlicedEndpointIdentity.lean`, `Estimates/AuxiliaryIntervalCells.lean`, `Estimates/BooleanMinorDimension.lean`, `Estimates/CanonicalCubeMinorThreshold.lean`, `Estimates/CoefficientJetScalar.lean`, `Estimates/CoefficientNormalization.lean`, `Estimates/CoefficientTailScaling.lean`, `Estimates/InitializedEarlyCanonicalSliceScales.lean`, `Estimates/InteriorIntervalCutoff.lean`, `Estimates/JointBooleanGoodWeight.lean`, `Estimates/PartialComplexScaledQuadrature.lean`, `Estimates/PreparedRelativeEndpointNumericalBounds.lean`, `Estimates/PreparedScalarNestedPowerDetection.lean`, `Estimates/ProductCutoffLipschitz.lean`, `Estimates/RawSourceTolerance.lean`, `Estimates/RowRestrictedDeckSiteMask.lean`, `Estimates/ScalarCubeFaceSlab.lean`, `Estimates/SelectedCoefficientEvaluation.lean`, `Estimates/SiteTwistCommonModulus.lean`, `Estimates/SplitSmoothProductProfile.lean`, `Fourier/CommonCoveredSiteCharacter.lean`, `Fourier/FiniteFourierSmoothing.lean`, `Fourier/FixedPrincipalCoefficientSpectrum.lean`, `Fourier/IntegerPeriodicTorusLift.lean`, `Fourier/LatticeTorusFourierCoefficient.lean`, `Fourier/MonomialCharacterMean.lean`, `Fourier/UniformScaledRetainedCharacters.lean`, `Geometry/CoveredJetChart.lean`, `Geometry/FiniteUniformCoordinateRefresh.lean`, `Geometry/MixedCoefficientSmallSupport.lean`, `Geometry/PhysicalBoxPartition.lean`, `Lattices/AffineBooleanCubeComparison.lean`, `Lattices/AffineCoefficientReindex.lean`, `Lattices/AffineCubeMinorGoodMass.lean`, `Lattices/BoxResiduePartition.lean`, `Lattices/ConcreteAffineMeshBoundary.lean`, `Lattices/CubeResidueSupport.lean`, `Lattices/IntegerFiberUniformBound.lean`, `Lattices/JointAffineBooleanSource.lean`, `Lattices/JointAffineBooleanTolerance.lean`, `Lattices/JointAffineL1Parameter.lean`, `Lattices/JointAffineUnitSource.lean`, `Lattices/LatticeDualCoordinates.lean`, `Lattices/OriginalKernelResidueRetained.lean`, `Lattices/PartitionedAffineLogEnvelope.lean`, `Lattices/PrimeCoordinateCells.lean`, `Lattices/PrincipalResidueMixture.lean`, `Lattices/ResidueCoefficientFamily.lean`, `Lattices/ResidueSliceCountingCost.lean`, `Lattices/ScalarResidueInteriorCell.lean`, `Lattices/SmoothAffinePairLaw.lean`, `Linear/FixedSpatialKernelSliceDensity.lean`, `Linear/KernelCoefficientDensity.lean`, `Polynomial/BooleanBlockCoefficientPhase.lean`, `Polynomial/JointBooleanPolynomialPerturbation.lean`, `Polynomial/PreparedEndpointPerturbationPolynomial.lean`, `Polynomial/RawCanonicalNormalizedPolynomial.lean`, `Probability/AnisotropicCanonicalDensity.lean`, `Probability/AnisotropicSpatialLaw.lean`, `Probability/BlockCubeDensity.lean`, `Probability/ObservedProductDensity.lean`, `Probability/ScaledInputProbability.lean`, `Probability/SlicedRemainderDensityFamily.lean`, `Sampling/BooleanProductSampler.lean`, `Sampling/BufferedScalarScoreBound.lean`, `Sampling/CanonicalSamplerTuple.lean`, `Sampling/ForecastContinuousRetainedExpansion.lean`, `Sampling/LayerSamplerWitnessScale.lean`, `Sampling/PreparedCenteredForecastSpatialBounds.lean`, `Sampling/SmoothSplitSampling.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B038
import Definitions.Def_OAIE3v2B039
import Definitions.Def_OAIE3v2B040
import Definitions.Def_OAIE3v2B044
import Definitions.Def_OAIE3v2B045
import Definitions.Def_OAIE3v2B046
import Definitions.Def_OAIE3v2B047
import Definitions.Def_OAIE3v2B048
import Definitions.Def_OAIE3v2B049
import Definitions.Def_OAIE3v2B056
import Definitions.Def_OAIE3v2B058
import Definitions.Def_OAIE3v2B059
import Definitions.Def_OAIE3v2B060
import Definitions.Def_OAIE3v2B061
import Definitions.Def_OAIE3v2B063
import Definitions.Def_OAIE3v2B064
import Definitions.Def_OAIE3v2B065
import Definitions.Def_OAIE3v2B066
import Definitions.Def_OAIE3v2B067

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PartialComplexScaledQuadrature
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J : Type*} [Fintype J]

theorem scaledRectangularWeight_summable (f : (J → ℝ) → ℝ) (c T : J → ℝ)
    {m : ℝ} (hm : 0 < m) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    Summable (fun z : J → ℤ => f (fun j => (c j + m * z j) / T j)) := by
  have h := rectangularWeight_summable f (fun j => -c j / m) (fun j => T j / m)
    (fun j => div_pos (hT j) hm) hsupport
  unfold rectangularWeight at h
  simpa only [rectangularLatticePoint_scaled c T hm.ne'] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerFiberUniformBound
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix BigOperators NNReal

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def normalizedFiberDensity (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i)
    (f : (J → ℝ) × (I → ℝ) → ℝ) : (I → ℝ) → ℝ :=
  pivotOutputDensity (normalizedPivotEquiv A hA S P hS hP)
    (matrixSupCLM (normalizedIntegerColumns B T P)) f

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

theorem scaledIntegerWeight_summable (f : (J → ℝ) × (I → ℝ) → ℝ) (S : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j) {R : ℝ}
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) : Summable (scaledIntegerWeight f S T) := by
  let e : (J ⊕ I → ℤ) ≃ (I → ℤ) × (J → ℤ) :=
    (Equiv.sumPiEquivProdPi (fun _ : J ⊕ I => ℤ)).trans (Equiv.prodComm _ _)
  have hscale : ∀ k, 0 < Sum.elim T S k := by intro k; cases k <;> simp [hS, hT]
  have h := scaledRectangularWeight_summable (splitInputProfile f) (fun _ => 0)
    (Sum.elim T S) (m := 1) zero_lt_one hscale (splitInputProfile_zero_outside hsupport)
  have heq (z : J ⊕ I → ℤ) : scaledIntegerWeight f S T (e z) =
      splitInputProfile f (fun k => (z k : ℝ) / Sum.elim T S k) := rfl
  have hs : Summable (fun z => scaledIntegerWeight f S T (e z)) := by
    simpa only [heq, zero_add, one_mul] using h
  exact e.summable_iff.mp hs

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FiniteFourierSmoothing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteImageCharacteristic {X H : Type*} [Fintype X] [AddCommGroup H]
    (p : FiniteProbabilityWeights X) (Y : X → H) (χ : AddChar H ℂ) : ℂ :=
  p.complexMean (fun x => χ (Y x))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost
namespace OAI

section

namespace Erdos3

theorem compatibleAuxResidueOfPoint_eq_iff (M d : ℕ) (hd : 0 < d) (u x : ℤ)
    (hx : x ≡ u [ZMOD (M : ℤ)]) (v : CompatibleAuxResidue M d u) :
    compatibleAuxResidueOfPoint M d hd u x hx = v ↔
      x ≡ (v.val.val : ℤ) [ZMOD (d : ℤ)] := by
  rw [Subtype.ext_iff]
  exact integerResidueLabel_eq_iff d hd x v.val

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoxResiduePartition
namespace OAI

section

namespace Erdos3

theorem intervalResidueCell_eq_iff (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N)
    (hstep : ∀ k, P.step k = 1) (r v : ℤ)
    (x : ↥(Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a (a + N)))) (k : P.Label) :
    intervalResidueCell a P r v x = k ↔
      intervalCellLower a P k ≤ x.val ∧ x.val < intervalCellUpper a P k := by
  let y := integerIntervalEquivFin a N ⟨x.val, (Finset.mem_filter.mp x.property).1⟩
  have hy : (y.val : ℤ) = x.val - a := integerIntervalEquivFin_val a N _
  change P.cell y = k ↔ _
  rw [P.cell_eq_iff_of_step_one hstep]
  unfold intervalCellLower intervalCellUpper
  constructor
  · rintro ⟨hlo, hhi⟩
    have hlo' : (P.start k : ℤ) ≤ y.val := by exact_mod_cast hlo
    have hhi' : (y.val : ℤ) < (P.start k : ℤ) + P.length k := by exact_mod_cast hhi
    omega
  · rintro ⟨hlo, hhi⟩
    constructor
    · have h : (P.start k : ℤ) ≤ y.val := by omega
      exact_mod_cast h
    · have h : (y.val : ℤ) < (P.start k : ℤ) + P.length k := by omega
      exact_mod_cast h

noncomputable def intervalResidueCellEquiv (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N)
    (hstep : ∀ k, P.step k = 1) (hpos : ∀ k, 0 < P.length k) (r v : ℤ) (k : P.Label) :
    {x : ↥(Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a (a + N))) //
      intervalResidueCell a P r v x = k} ≃
      ↥(Finset.filter (fun x => x ≡ v [ZMOD r])
        (Finset.Ico (intervalCellLower a P k) (intervalCellUpper a P k))) where
  toFun x := ⟨x.val.val, Finset.mem_filter.mpr
    ⟨Finset.mem_Ico.mpr ((intervalResidueCell_eq_iff a P hstep r v x.val k).mp x.property),
      (Finset.mem_filter.mp x.val.property).2⟩⟩
  invFun x := by
    have hx := Finset.mem_filter.mp x.property
    have hinterval := Finset.mem_Ico.mp hx.1
    have hend := P.end_le_of_step_one hstep k (hpos k)
    have hend' : (P.start k : ℤ) + P.length k ≤ N := by exact_mod_cast hend
    have hstart : (0 : ℤ) ≤ P.start k := Int.natCast_nonneg _
    have houter : x.val ∈ Finset.Ico a (a + N) := by
      simp only [intervalCellLower, intervalCellUpper] at hinterval
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    let y : ↥(Finset.filter (fun z => z ≡ v [ZMOD r]) (Finset.Ico a (a + N))) :=
      ⟨x.val, Finset.mem_filter.mpr ⟨houter, hx.2⟩⟩
    exact ⟨y, (intervalResidueCell_eq_iff a P hstep r v y k).mpr hinterval⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def boxIntervalResidueCell {I : Type*} (a : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (r v : I → ℤ)
    (x : IntegerResidueBox a (fun i => a i + N i) r v) : ∀ i, (P i).Label :=
  fun i => intervalResidueCell (a i) (P i) (r i) (v i) (x i)

noncomputable def boxIntervalResidueCellEquiv {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1) (hpos : ∀ i k, 0 < (P i).length k)
    (r v : I → ℤ) (k : ∀ i, (P i).Label) :
    ↥(partitionCell (boxIntervalResidueCell a N P r v) k) ≃
      IntegerResidueBox (fun i => intervalCellLower (a i) (P i) (k i))
        (fun i => intervalCellUpper (a i) (P i) (k i)) r v := by
  let e₁ : ↥(partitionCell (boxIntervalResidueCell a N P r v) k) ≃
      {x : IntegerResidueBox a (fun i => a i + N i) r v //
        ∀ i, intervalResidueCell (a i) (P i) (r i) (v i) (x i) = k i} :=
    Equiv.subtypeEquivRight (fun x => by
      simp only [mem_partitionCell, boxIntervalResidueCell, funext_iff])
  exact e₁.trans (Equiv.subtypePiEquivPi.trans (Equiv.piCongrRight (fun i =>
    intervalResidueCellEquiv (a i) (P i) (hstep i) (hpos i) (r i) (v i) (k i))))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.BooleanProductSampler
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
  [DecidableEq B] [DecidableEq F] [DecidableEq α]

noncomputable def booleanSelectedColumn (c : B → ℝ) (b : B) (v : F) (r : Option α) (s : Finset α) :
    MvPolynomial (BlockParameter B F α) ℝ :=
  MvPolynomial.C (c b) * booleanCoefficient
    (fun t => MvPolynomial.C (booleanFeature r t : ℝ) *
      ∏ k ∈ Finset.univ.erase v, booleanAffinePolynomial b k t) s

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BooleanBlockCoefficientPhase
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def frozenBooleanFactor {G α : Type*} [Fintype α] [DecidableEq α]
    (label : G → Option α) (c : G → Option α → ℝ) (t : Finset α) (g : G) : MvPolynomial G ℝ :=
  MvPolynomial.C (booleanFeature (label g) t : ℝ)*MvPolynomial.X g +
    MvPolynomial.C (frozenBooleanConstant label c t g)

noncomputable def frozenBooleanPhasePolynomial {G α : Type*} [Fintype G]
    [Fintype α] [DecidableEq α]
    (label : G → Option α) (c : G → Option α → ℝ) (ξ : Finset α → ℝ) : MvPolynomial G ℝ :=
  ∑ s, MvPolynomial.C (ξ s) * booleanCoefficient (fun t => ∏ g, frozenBooleanFactor label c t g) s

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanMinorDimension
namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff

variable {B F α O : Type*} [Fintype B] [Fintype F] [Fintype α]
  [DecidableEq B] [DecidableEq F] [DecidableEq α]

noncomputable def booleanSelectedMinor (c : B → ℝ) (sets : O → Finset α)
    (block : O → B) (v : F) (r : O → Option α) : Matrix O O (MvPolynomial (BlockParameter B F α) ℝ) :=
  fun row col => MvPolynomial.pderiv (block col, v, r col) (booleanSamplerPolynomial c (sets row))

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

noncomputable def booleanMinorDeterminant {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (v : F) (r : O → Option α)
    (a : BlockParameter B F α → ℝ) : ℝ :=
  ((booleanSelectedMinor c sets block v r).map (MvPolynomial.eval a)).det

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarCubeFaceSlab
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem closedScalarCubeDomain_coordinate_abs_le_one {α : Type*} [Fintype α] [DecidableEq α]
    {a : Option α → ℝ} (ha : a ∈ closedScalarCubeDomain α) (r : Option α) : |a r| ≤ 1 := by
  have hzero := ha ∅
  rw [scalarCubeValue_empty] at hzero
  cases r with
  | none => exact abs_le.mpr ⟨by linarith [hzero.1], hzero.2⟩
  | some i =>
    have hi := ha {i}
    rw [scalarCubeValue_singleton] at hi
    exact abs_le.mpr ⟨by linarith [hzero.2, hi.1], by linarith [hzero.1, hi.2]⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Classical

theorem halfOpenScalarCubeDomain_subset_closed (I : Type*) [Fintype I] [DecidableEq I] :
    halfOpenScalarCubeDomain I ⊆ closedScalarCubeDomain I :=
  fun _ hx t => ⟨(hx t).1, (hx t).2.le⟩

theorem halfOpenScalarCubeDomain_norm_le {I : Type*} [Fintype I] [DecidableEq I]
    {x : Option I → ℝ} (hx : x ∈ halfOpenScalarCubeDomain I) : ‖x‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  exact closedScalarCubeDomain_coordinate_abs_le_one (halfOpenScalarCubeDomain_subset_closed I hx) i

theorem scalarCubeIndicator_zero_outside (I : Type*) [Fintype I] [DecidableEq I]
    (x : Option I → ℝ) (hx : 1 < ‖x‖) : scalarCubeIndicator I x = 0 := by
  apply if_neg
  exact fun h => (not_lt_of_ge (halfOpenScalarCubeDomain_norm_le h)) hx

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductCutoffLipschitz
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

noncomputable def scalarCubeProductCutoff {ι : Type*} [Fintype ι]
    (α : Type*) [Fintype α] [DecidableEq α] (r : ι → ℝ) : (ι → Option α → ℝ) → ℝ :=
  tensorCutoffWeight (fun i => inequalityBoundaryCutoff
    (fun _ : Bool × Finset α => r i) scalarCubeFace)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarCubeBoundaryLogBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

noncomputable def scalarCubeProductBoundaryRadius (ι α : Type*) [Fintype ι] [Fintype α]
    [DecidableEq α] (η : ℝ) : ℝ :=
  η / (scalarCubeBoundaryConstant α * ((Fintype.card ι : ℝ) + 1))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientNormalization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def booleanCoefficientTail {T K I α : Type*} [Fintype α] [DecidableEq α]
    (terms : Finset T) (coefficient : T → MvPolynomial I ℝ)
    (exponent : T → K →₀ ℕ) (input : K → Option α → MvPolynomial I ℝ)
    (s : Finset α) : MvPolynomial I ℝ :=
  booleanCoefficient (fun t => ∑ n ∈ terms,
    coefficient n * polynomialMonomial (fun k => booleanAffineInput (input k) t) (exponent n)) s

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def normalizedCoefficientTail {T K Z I α : Type*} [Fintype α] [DecidableEq α]
    (terms : Finset T) (weight : T → ℝ) (exponent : T → K →₀ ℕ)
    (coefficientIndex : T → Z) (inputIndex : K → Option α → Z ⊕ I) (s : Finset α) :
    MvPolynomial (PolynomialParameter Z I) ℝ :=
  booleanCoefficientTail terms
    (fun n => MvPolynomial.C (weight n) * MvPolynomial.X (some (.inl (coefficientIndex n))))
    exponent (fun k r => MvPolynomial.X (some (inputIndex k r))) s

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CanonicalSamplerTuple
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def canonicalTupleInput {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}
    (extra : G → Option α → Z) : SamplerTupleIndex G B h → Option α → Z ⊕ JointBlockParameter B h α
  | .inl g, r => .inl (extra g r)
  | .inr ⟨d, b, v⟩, r => .inr ⟨d, b, v, r⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointBooleanGoodWeight
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def blockCubeWeight {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    (w : ((B × F) → Option α → ℝ) → ℝ) (a : BlockParameter B F α → ℝ) : ℝ :=
  w ((blockCubeFlatten B F α).symm a)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SlicedRemainderDensityFamily
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {D : Type*} [Fintype D] {I O : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, Fintype (O d)]

instance sigmaAxisMeasure_probability (μ : ∀ d, Measure (I d → ℝ))
    [∀ d, IsProbabilityMeasure (μ d)] : IsProbabilityMeasure (sigmaAxisMeasure μ) := by
  unfold sigmaAxisMeasure
  exact Measure.isProbabilityMeasure_map (sigmaAxisCoordinates I).symm.continuous.measurable.aemeasurable

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.JointBooleanPolynomialPerturbation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {D α : Type*} [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)]

noncomputable def jointBooleanPolynomial (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (o : Σ d, O d) :
    MvPolynomial (JointBlockParameter B h α) ℝ :=
  MvPolynomial.rename (Sigma.mk o.1)
    (booleanSamplerPolynomial (F := Fin (h o.1)) (c o.1) (sets o.1 o.2))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D α Z : Type*} [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)]

noncomputable def jointBooleanPerturbedPolynomial (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α)
    (r : (Σ d, O d) → MvPolynomial (PolynomialParameter Z (JointBlockParameter B h α)) ℝ)
    (o : Σ d, O d) : MvPolynomial (PolynomialParameter Z (JointBlockParameter B h α)) ℝ :=
  scalePerturbedPolynomial (jointBooleanPolynomial h c sets o) (r o)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientTailScaling
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {D K Z α : Type*} [Fintype α] [DecidableEq α]
  {B O T : D → Type*} [∀ d, Fintype (B d)]

noncomputable def jointCoefficientTail (h : D → ℕ) (sets : ∀ d, O d → Finset α)
    (terms : ∀ d, Finset (T d)) (weight : ∀ d, T d → ℝ) (exponent : ∀ d, T d → K →₀ ℕ)
    (coefficientIndex : ∀ d, T d → Z)
    (inputIndex : K → Option α → Z ⊕ JointBlockParameter B h α) (o : Σ d, O d) :
    MvPolynomial (PolynomialParameter Z (JointBlockParameter B h α)) ℝ :=
  normalizedCoefficientTail (terms o.1) (weight o.1) (exponent o.1) (coefficientIndex o.1)
    inputIndex (sets o.1 o.2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RawCanonicalNormalizedPolynomial
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def nonprincipalSupport {K J : Type*} [Fintype J]
    (p : MvPolynomial K ℝ) (principal : J → K →₀ ℕ) : Finset (K →₀ ℕ) := by
  classical
  exact p.support \ insert 0 (Finset.univ.image principal)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedCoefficientEvaluation
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

noncomputable def smoothSplitProfile (J I : Type*) [Fintype J] [Fintype I]
    (p : (J → ℝ) × (I → ℝ)) : ℝ :=
  smoothProductProfile J p.1 * smoothProductProfile I p.2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledInputProbability
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Matrix BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def scaledInputPMF (f : (J → ℝ) × (I → ℝ) → ℝ) (hf0 : ∀ p, 0 ≤ f p)
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hM : 0 < scaledInputMass f S T) :
    PMF ((I → ℤ) × (J → ℤ)) :=
  realWeightPMF (scaledIntegerWeight f S T) (fun _ => hf0 _)
    (scaledIntegerWeight_summable f S T hS hT hsupport) (scaledInputWeightSum_pos f S T hS hT hM)

noncomputable def integerImagePMF (A : Matrix I I ℤ) (B : Matrix I J ℤ)
    (f : (J → ℝ) × (I → ℝ) → ℝ) (hf0 : ∀ p, 0 ≤ f p)
    (S : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ p, R < ‖p‖ → f p = 0) (hM : 0 < scaledInputMass f S T) :
    PMF (I → ℤ) :=
  (scaledInputPMF f hf0 S T hS hT hsupport hM).map (fun p => A *ᵥ p.1 + B *ᵥ p.2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SmoothSplitSampling
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem smoothSampleSum_pos {S : ℝ} (hS : 0 < S) : 0 < smoothSampleSum S := by
  have h := (smoothProfileSamples_summable hS).le_tsum 0
    (fun k _ => (smoothProbabilityProfile_range _).1)
  simp only [Int.cast_zero, zero_div] at h
  exact smoothProbabilityProfile_pos_zero.trans_le h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothProductSamples_summable {I : Type*} [Fintype I]
    (S : I → ℝ) (hS : ∀ i, 0 < S i) :
    Summable (fun z : I → ℤ => smoothProductProfile I (fun i => (z i : ℝ) / S i)) := by
  have h := rectangularWeight_summable (smoothProductProfile I) (fun _ => 0) S hS
    (smoothProductProfile_zero_outside I)
  change Summable (fun z : I → ℤ =>
    smoothProductProfile I (fun i => ((z i : ℝ) - 0) / S i)) at h
  simpa only [sub_zero] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


namespace Erdos3

noncomputable def integerScalarCubeEquiv (q L : ℕ) :
    ↥(integerScalarCubeSet (Fin q) L) ≃ SupportedCube q (Set.Ico (0 : ℤ) (L : ℤ)) where
  toFun x := ⟨(fun i => (x.val (some i) : ℤ), (x.val none : ℤ)),
    (integerScalarCube_iff_supported q L _).mp ((mem_integerScalarCubeSet L _).mp x.property)⟩
  invFun p := by
    let v : Option (Fin q) → ℤ := fun | none => p.val.2 | some i => p.val.1 i
    have hv : IntegerScalarCube L v := (integerScalarCube_iff_supported q L v).mpr p.property
    let x : IntegerScalarCubeBox (Fin q) L := fun i =>
      ⟨v i, Finset.mem_Ico.mpr ⟨(integerScalarCube_coordinates hv i).1.le,
        (integerScalarCube_coordinates hv i).2⟩⟩
    exact ⟨x, (mem_integerScalarCubeSet L x).mpr hv⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    cases i <;> rfl
  right_inv p := by
    apply Subtype.ext
    rfl


open scoped BigOperators Classical

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothAffinePairLaw
namespace OAI


namespace Erdos3

open MeasureTheory
open scoped Matrix NNReal BigOperators

noncomputable def affinePairRowDensity {J : Type*} [Fintype J] [DecidableEq J]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0) (H L : ℝ) (hH : 0 < H) (hL : 0 < L)
    (f : ({j : J // j ≠ k} → ℝ) × (Fin 2 → ℝ) → ℝ) : (Fin 2 → ℝ) → ℝ :=
  normalizedFiberDensity (affinePairPivot t u k) (by rwa [affinePairPivot_det])
    (affinePairFree t u k) (affinePairScale H L) (fun _ => H) (fun _ => H / L)
    (affinePairScale_pos hH hL) (fun _ => hH) f

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InteriorIntervalCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem interiorIntervalCutoff_range (eta : ℝ≥0) (x : ℝ) :
    0 ≤ interiorIntervalCutoff eta x ∧ interiorIntervalCutoff eta x ≤ 1 :=
  linearCutoff_range _ _ _

theorem interiorIntervalCutoff_support (eta : ℝ≥0) {x : ℝ}
    (hx : interiorIntervalCutoff eta x ≠ 0) : (eta : ℝ) < x ∧ x < 1 - eta := by
  have h : |x - 1 / 2| < 1 / 2 - eta := by
    by_contra h
    apply hx
    exact linearCutoff_eq_zero _ _ (by linarith [le_of_not_gt h])
  exact ⟨by linarith [(abs_lt.mp h).1], by linarith [(abs_lt.mp h).2]⟩

theorem interiorIntervalCutoff_lipschitz (eta : ℝ≥0) (heta : 0 < eta) :
    LipschitzWith eta⁻¹ (interiorIntervalCutoff eta) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply ((linearCutoff_lipschitz _ eta heta).dist_le_mul _ _).trans
  apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg _)
  rw [Real.dist_eq]
  exact (abs_abs_sub_abs_le_abs_sub _ _).trans_eq (by rw [sub_sub_sub_cancel_right]; rfl)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformScaledRetainedCharacters
namespace OAI

section

namespace Erdos3

noncomputable def localizedMajorArcErrorBudget (n : ℕ) (U ζ : ℝ) : ℝ :=
  localizedMajorArcBudget n U ζ *
    (localizationLengthBudget U (localizationThreshold U ζ (n + 1)) 1) ^ (n + 1)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.IntegerPeriodicTorusLift
namespace OAI

section

namespace Erdos3

variable {ι : Type*}

theorem continuous_integerPeriodicTorusLift (F : (ι → ℝ) → ℂ) (hc : Continuous F)
    (hF : ∀ (x : ι → ℝ) (n : ι → ℤ), F (fun i => x i + (n i : ℝ)) = F x) :
    Continuous (integerPeriodicTorusLift F) := by
  have hq : IsOpenQuotientMap (fun x : ι → ℝ => fun i => (x i : UnitAddCircle)) :=
    IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)
  apply hq.isQuotientMap.continuous_iff.mpr
  convert hc using 1
  funext x
  exact integerPeriodicTorusLift_coe F hF x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CommonCoveredSiteCharacter
namespace OAI

section

namespace Erdos3

variable {D : Type*} [Fintype D] (U : Submodule ℝ (D → ℝ))

omit [Fintype D] in
theorem euclideanSubspaceArrayEquiv_apply (x : euclideanSubspace U) (u : Unit) (i : D) :
    (euclideanSubspaceArrayEquiv U x u).val i = x.val i := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoefficientSmallSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule

variable {D : Type*} [Fintype D] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)

def normalizedChartRegion (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (Ω : Set (EuclideanSpace ℝ D)) :
    Set (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) :=
  normalizedLatticeQuotient W b hb '' (normalizedLatticePoint W b ⁻¹' Ω)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PositiveModerateBudget
namespace OAI

section

namespace Erdos3

noncomputable def positiveModerateLengthConstant (n : ℕ) (U : ℝ) : ℝ :=
  1 + majorArcLengthConstant n U + majorArcLengthConstant (n + 1) U

noncomputable def positiveModerateCoverConstant (n j : ℕ) (U V : ℝ) : ℝ :=
  (1 + majorArcLengthConstant (n + 1) U) * majorArcCoverConstant n j U (4 * V) +
    majorArcCoverConstant (n + 1) j U V

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrincipalResidueMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def principalResidueLabel {D α : Type*} {B : D → Type*} {h : D → ℕ}
    {L : PrincipalTupleIndex B h → ℕ} (m : ℕ) (y : PrincipalIntegerTuples B h α L) :
    PrincipalTupleIndex B h → Option α → ZMod m := fun j i => ((y j i : ℤ) : ZMod m)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalBoxPartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def physicalBoxCell (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (x : translatedIntegerBox lo N) : ∀ i, (P i).Label :=
  boxIntervalResidueCell lo N P (fun _ => 1) (fun _ => 0) (physicalBoxUnitResidueEquiv lo N x)

noncomputable def physicalBoxCellEquiv (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (c : ∀ i, (P i).Label) :
    {x : translatedIntegerBox lo N // physicalBoxCell lo N P x = c} ≃
      IntegerResidueBox (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => intervalCellLower (lo i) (P i) (c i) + (P i).length (c i))
        (fun _ => 1) (fun _ => 0) := by
  let e : {x : translatedIntegerBox lo N // physicalBoxCell lo N P x = c} ≃
      ↥(partitionCell (boxIntervalResidueCell lo N P (fun _ => 1) (fun _ => 0)) c) :=
    (physicalBoxUnitResidueEquiv lo N).subtypeEquiv (fun x =>
      (mem_partitionCell (boxIntervalResidueCell lo N P (fun _ => 1) (fun _ => 0)) c
        (physicalBoxUnitResidueEquiv lo N x)).symm)
  exact e.trans (boxIntervalResidueCellEquiv lo N P hstep hpos (fun _ => 1) (fun _ => 0) c)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedProductDensity
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*} [∀ i, Fintype (X i)]

theorem productFiberMass_nonneg (w : (∀ i, X i) → ℝ) (hw : ∀ x, 0 ≤ w x)
    (S : Finset I) (x : ∀ i, X i) : 0 ≤ productFiberMass w S x := by
  apply Finset.sum_nonneg
  intro y _
  apply mul_nonneg (hw y)
  unfold productFiberIndicator
  split_ifs <;> norm_num

theorem productFiberMass_empty (w : (∀ i, X i) → ℝ) (x : ∀ i, X i) :
    productFiberMass w ∅ x = ∑ y, w y := by
  simp [productFiberMass, productFiberIndicator]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarResidueInteriorCell
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem integerScalarCube_iff_normalized {I : Type*} [Fintype I] [DecidableEq I]
    {L : ℕ} (hL : 0 < L) (z : Option I → ℤ) :
    IntegerScalarCube L z ↔ (fun i => (z i : ℝ) / L) ∈ halfOpenScalarCubeDomain I := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have he (t : Finset I) : scalarCubeValue (fun i => (z i : ℝ) / L) t = (integerScalarCubeValue z t : ℝ) / L := by
    simp only [scalarCubeValue_formula, integerScalarCubeValue, Int.cast_add, Int.cast_sum, add_div, Finset.sum_div]
  constructor
  · intro hz t
    rw [he]
    constructor
    · exact div_nonneg (by exact_mod_cast (hz t).1) hLp.le
    · exact (div_lt_one hLp).mpr (by exact_mod_cast (hz t).2)
  · intro hz t
    have ht := hz t
    rw [he] at ht
    constructor
    · have hh : (0 : ℝ) ≤ (integerScalarCubeValue z t : ℝ) := by
        simpa only [zero_mul] using (le_div_iff₀ hLp).mp ht.1
      exact_mod_cast hh
    · exact_mod_cast (div_lt_one hLp).mp ht.2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.LayerSamplerWitnessScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

theorem exists_layerSamplerScale (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (L₀ : ℕ) : ∃ S : LayerSamplerScale (G := G) B U b R σ,
      L₀ ≤ S.value ∧ S.value ≤ layerSamplerScaleBound (G := G) B R σ L₀ := by
  obtain ⟨L, hL, hlo, hhi, hw, hg⟩ := exists_common_polynomial_scale
    (fun a : Σ j, Fin (n j) => basisAxisScale (b a.1) a.2) (fun a => a.1.val + 1)
    (layerSamplerGapWidth (G := G) B R) (layerSamplerTailWidth (G := G) B R σ)
    (fun j => tailProfileSize_pos (hR j) (hσ j) _) L₀
  exact ⟨⟨L, hL, hw, fun j i => hg ⟨j, i⟩⟩, hlo, hhi⟩

noncomputable def selectedLayerSamplerScale (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j)
    (hσ : ∀ j, 0 < σ j) (L₀ : ℕ) : LayerSamplerScale (G := G) B U b R σ :=
  (exists_layerSamplerScale (G := G) B U b R σ hR hσ L₀).choose

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.BlockCubeDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory

def blockCubeDomain (B F α : Type*) [Fintype B] [Fintype F] [Fintype α] [DecidableEq α] :
    Set (BlockParameter B F α → ℝ) :=
  (blockCubeFlatten B F α).symm ⁻¹' scalarCubeProductDomain (B × F) α

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalCubeMinorThreshold
namespace OAI

section

namespace Erdos3

noncomputable def cubeMinorProbabilityConstant (O α : Type*) [Fintype O] [Fintype α]
    [DecidableEq α] (h N d : ℕ) : ℝ :=
  scalarCubeDomainDensity α ^ Fintype.card (O × Fin h) * multivariateSublevelConstant N d

noncomputable def cubeMinorThreshold (J O α : Type*) [Fintype J] [Fintype O] [Fintype α]
    [DecidableEq α] (h N d : ℕ) (c₀ η : ℝ) : ℝ :=
  polynomialSublevelThreshold (N * d) (Fintype.card J)
    (cubeMinorProbabilityConstant O α h N d) (cubeMinorProbabilityScale O N d c₀) η

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def canonicalCubeMinorThreshold (J O α : Type*)
    [Fintype J] [Fintype O] [Fintype α] [DecidableEq α] (h : ℕ) (c₀ η : ℝ) : ℝ :=
  cubeMinorThreshold J O α h (cubeMinorVariableCount O α h) (cubeMinorDegree O h) c₀ η

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RawSourceTolerance
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def booleanToleranceC2 {D α : Type*} [Fintype D] [Fintype α]
    {B : D → Type*} [∀ d, Fintype (B d)] (Z : Type*) [Fintype Z]
    (h : D → ℕ) (degree : ℕ) (Csum Wsum : ℝ) : ℝ :=
  polynomialC2BoxBudget (Fintype.card (PolynomialParameter Z (JointBlockParameter B h α)))
    (degree+2) (booleanJetMassBudget (Fintype.card α) degree Csum+
      booleanJetMassBudget (Fintype.card α) degree Wsum)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.JointAffineL1Parameter
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def affineSelectedJetProfile {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (c w : J ⊕ N → ℝ) : (UnselectedColumn s ⊕ N → ℝ) × (I → ℝ) → ℝ :=
  splitFreeProfile
    (selectedCoefficientProfile s (affineProductProfile (fun j => c (.inl j)) (fun j => w (.inl j))))
    (affineProductProfile (fun n => c (.inr n)) (fun n => w (.inr n)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelCoefficientDensity
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def kernelCoefficientDensity {I J N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (C : Matrix I N ℤ) (T : N → ℝ) (c w : J ⊕ N → ℝ) : (I → ℝ) → ℝ :=
  pivotOutputDensity
    (normalizedPivotEquiv (A.submatrix id s) hA (fun i => S (s i)) P (fun i => hS (s i)) hP)
    (splitFreeColumns
      (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) P))
      (matrixSupCLM (normalizedIntegerColumns C T P)))
    (splitFreeProfile
      (selectedCoefficientProfile s (affineProductProfile (fun j => c (.inl j)) (fun j => w (.inl j))))
      (affineProductProfile (fun n => c (.inr n)) (fun n => w (.inr n))))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueCoefficientFamily
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def coefficientReplacementScale {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (b t ε L : ℝ) (h : ℕ) : ℝ :=
  Real.exp (coefficientLogAllowance (Fintype.card I) (Fintype.card (UnselectedColumn s))
    (affineCoefficientCommonBudget (Fintype.card J) (Fintype.card (UnselectedColumn s)) b t)) *
      (1+ε⁻¹) * L^(h*(Fintype.card I+1))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CandidateCommonFastBudgetMonotonicity
namespace OAI

section

namespace Erdos3

theorem allocatedCandidateCommonFastGeometryLog_mono {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) :
    allocatedCandidateCommonFastGeometryLog p ≤ allocatedCandidateCommonFastGeometryLog q := by
  have hinput := allocatedCandidateCommonFastSectionInput_mono hp hpq
  have hnonneg := (allocatedCandidateCommonFastSectionInput_bounds hp).1
  unfold allocatedCandidateCommonFastGeometryLog
  exact add_le_add
    (pow_le_pow_left₀ (by positivity : 0 ≤ allocatedCandidateCommonFastSectionInput p + 2)
      (add_le_add hinput (le_refl 2)) 47) (le_refl 1)

theorem allocatedCandidateCommonFastBudget_mono (s : ℕ) {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) :
    allocatedCandidateCommonFastBudget s p ≤ allocatedCandidateCommonFastBudget s q := by
  exact add_le_add (allocatedCandidateCommonFastGeometryLog_mono hp hpq)
    (NilpotentLieFiltration.pointwiseFastSectionInput_mono s hp hpq)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientJetScalar
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}

instance coefficientJetScalarMeasurable (a : LayerSamplerAxis I n) :
    MeasurableSpace (CoefficientJetScalar a) :=
  match a with
  | ⟨_, .inl _⟩ => inferInstanceAs (MeasurableSpace ℝ)
  | ⟨_, .inr _⟩ => inferInstanceAs (MeasurableSpace ℤ)

def coefficientJetScalarEquiv (O : Fin m → Type*) (a : LayerSamplerAxis I n) :
    CoefficientJetAxisRow O a ≃ᵐ (O a.1 → CoefficientJetScalar a) :=
  match a with
  | ⟨_, .inl _⟩ => MeasurableEquiv.refl _
  | ⟨_, .inr _⟩ => MeasurableEquiv.refl _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoveredJetChart
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {O J B : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))

instance coveredJetChartSource_borel [∀ j, Fintype (O j)] (d : ℕ) [NeZero d] :
    BorelSpace (CoveredJetChartSource U O B n d) := by
  let : ∀ j, BorelSpace ((euclideanSubspace (U j) × (Fin (n j) → ℤ)) × (B j → ZMod d)) :=
    fun _ => inferInstance
  let : ∀ j, BorelSpace (O j → (euclideanSubspace (U j) × (Fin (n j) → ℤ)) × (B j → ZMod d)) :=
    fun _ => Pi.borelSpace
  exact Pi.borelSpace

variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

def coveredJetTargetRegion (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j))) :
    Set (EuclideanJetLayers U O) :=
  Set.univ.pi (fun j => Set.univ.pi (fun t =>
    quotientIntegerCover
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup d ⁻¹'
        normalizedChartRegion (euclideanSubspace (U j)) (b j) (hb j) (Ω j t)))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AuxiliaryIntervalCells
namespace OAI

section

namespace Erdos3

theorem intervalAuxiliaryCell_eq_iff (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N)
    (hstep : ∀ k, P.step k = 1) (M d : ℕ) (hd : 0 < d) (u r b : ℤ)
    (hbase : ∀ x : ℤ, x ≡ b [ZMOD r] → x ≡ u [ZMOD (M : ℤ)])
    (x : ↥(Finset.filter (fun x => x ≡ b [ZMOD r]) (Finset.Ico a (a + N))))
    (k : P.Label × CompatibleAuxResidue M d u) :
    intervalAuxiliaryCell a P M d hd u r b hbase x = k ↔
      (intervalCellLower a P k.1 ≤ x.val ∧ x.val < intervalCellUpper a P k.1) ∧
        x.val ≡ (k.2.val.val : ℤ) [ZMOD (d : ℤ)] := by
  rcases k with ⟨j, v⟩
  simp only [intervalAuxiliaryCell, Prod.mk.injEq, intervalResidueCell_eq_iff a P hstep,
    compatibleAuxResidueOfPoint_eq_iff]

noncomputable def intervalAuxiliaryCellEquiv (a : ℤ) {N : ℕ} (P : FiniteProgressionPartition N)
    (hstep : ∀ k, P.step k = 1) (hpos : ∀ k, 0 < P.length k)
    (M d : ℕ) (hd : 0 < d) (u r b : ℤ)
    (hbase : ∀ x : ℤ, x ≡ b [ZMOD r] → x ≡ u [ZMOD (M : ℤ)])
    (k : P.Label × CompatibleAuxResidue M d u) (R c : ℤ)
    (hcombine : ∀ x : ℤ,
      (x ≡ b [ZMOD r] ∧ x ≡ (k.2.val.val : ℤ) [ZMOD (d : ℤ)]) ↔ x ≡ c [ZMOD R]) :
    {x : ↥(Finset.filter (fun x => x ≡ b [ZMOD r]) (Finset.Ico a (a + N))) //
      intervalAuxiliaryCell a P M d hd u r b hbase x = k} ≃
      ↥(Finset.filter (fun x => x ≡ c [ZMOD R])
        (Finset.Ico (intervalCellLower a P k.1) (intervalCellUpper a P k.1))) where
  toFun x := by
    have hx := (intervalAuxiliaryCell_eq_iff a P hstep M d hd u r b hbase x.val k).mp x.property
    exact ⟨x.val.val, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hx.1,
      (hcombine x.val.val).mp ⟨(Finset.mem_filter.mp x.val.property).2, hx.2⟩⟩⟩
  invFun x := by
    have hx := Finset.mem_filter.mp x.property
    have hinterval := Finset.mem_Ico.mp hx.1
    have hr := (hcombine x.val).mpr hx.2
    have hend := P.end_le_of_step_one hstep k.1 (hpos k.1)
    have hend' : (P.start k.1 : ℤ) + P.length k.1 ≤ N := by exact_mod_cast hend
    have hstart : (0 : ℤ) ≤ P.start k.1 := Int.natCast_nonneg _
    have houter : x.val ∈ Finset.Ico a (a + N) := by
      simp only [intervalCellLower, intervalCellUpper] at hinterval
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    let y : ↥(Finset.filter (fun z => z ≡ b [ZMOD r]) (Finset.Ico a (a + N))) :=
      ⟨x.val, Finset.mem_filter.mpr ⟨houter, hr.1⟩⟩
    exact ⟨y, (intervalAuxiliaryCell_eq_iff a P hstep M d hd u r b hbase y k).mpr
      ⟨hinterval, hr.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.JointAffineUnitSource
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def affineJetUnitMap {Z X K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [Fintype J] [Fintype N]
    (s : I ↪ J) (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (F : (UnselectedColumn s → ℝ) →L[ℝ] (I → ℝ))
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ)
    (rows : I → Finset α) (c w : J ⊕ N → ℝ) (x : X → ℝ) (r : J ⊕ N → ℝ) : I → ℝ :=
  A (fun i => c (.inl (s i))+w (.inl (s i))*r (.inl (s i))) +
    F (fun j => c (.inl j.val)+w (.inl j.val)*r (.inl j.val)) +
      polynomialColumns (fun o n => normalizedJetColumn (e n) input z (rows o)) x
        (fun n => c (.inr n)+w (.inr n)*r (.inr n))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RowRestrictedDeckSiteMask
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace VectorPolynomial

open Module Submodule

variable {m : ℕ} {I J E : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rows" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

noncomputable def mixedCoveredRowsSiteValue (d : ℕ)
    (z : MixedCoveredJetSource I rows E n d) (s : Finset α) :
    MixedCoveredJetSource I (fun _ => Unit) E n d :=
  mixedCoveredJetIntegerImage d (fun j (_ : Unit) => rowRestrictedSiteMatrix (rowSets j) s) z

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientReindex
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {I J O : Type*} [Fintype I] [Fintype J]

theorem affineProductProfile_reindex (e : I ≃ J) (c w x : J → ℝ) :
    affineProductProfile (c ∘ e) (w ∘ e) (x ∘ e) = affineProductProfile c w x :=
  Equiv.prod_comp e (fun j => affineProbabilityProfile (c j) (w j) (x j))

theorem affineCoefficientWeight_reindex (e : I ≃ J) (c w S : J → ℝ) (z : J → ℤ) :
    coefficientWeight (affineProductProfile (c ∘ e) (w ∘ e)) (S ∘ e) (z ∘ e) =
      coefficientWeight (affineProductProfile c w) S z :=
  affineProductProfile_reindex e c w (fun j => (z j : ℝ)/S j)

theorem affineCoefficientWeightSum_reindex (e : I ≃ J) (c w S : J → ℝ) :
    coefficientWeightSum (affineProductProfile (c ∘ e) (w ∘ e)) (S ∘ e) =
      coefficientWeightSum (affineProductProfile c w) S := by
  let E : (J → ℤ) ≃ (I → ℤ) := Equiv.arrowCongr e.symm (Equiv.refl ℤ)
  calc
    _ = ∑' z : J → ℤ,
        coefficientWeight (affineProductProfile (c ∘ e) (w ∘ e)) (S ∘ e) (z ∘ e) :=
      (E.tsum_eq _).symm
    _ = _ := tsum_congr (fun z => affineCoefficientWeight_reindex e c w S z)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AnisotropicSpatialLaw
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel

noncomputable def anisotropicSpatialKernelDensity {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    (A R L : ℝ) (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) : ((Unit ⊕ I) → ℝ) → ℝ :=
  normalizedFiberDensity (selectedSpatialPivot root D s) hp (selectedSpatialFreeColumns root D s)
    (anisotropicSpatialScale I A R) (physicalSpatialOutputScale I A R L) (fun _ => R)
    (anisotropicSpatialScale_pos I hA hR) (physicalSpatialOutputScale_pos I hA hR hL)
    (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AnisotropicCanonicalDensity
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel

noncomputable def canonicalSpatialKernelDensity {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    (W L : ℝ) (hW : 0 ≤ W) (hL : 0 < L) : ((Unit ⊕ I) → ℝ) → ℝ :=
  anisotropicSpatialKernelDensity s root D hp (1 + W) 1 L (by linarith) zero_lt_one hL

noncomputable def canonicalSpatialSiteDensity {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    (W L : ℝ) (hW : 0 ≤ W) (hL : 0 < L) : ((Unit ⊕ I) → ℝ) → ℝ :=
  coordinateRescaledDensity (fun i => (1 + W) / physicalSpatialOutputScale I (1 + W) 1 L i)
    (canonicalSpatialKernelDensity s root D hp W L hW hL)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

attribute [local instance] ScalarSiteExpansion.termFinite

variable {A D S : Type*} [Fintype A] [Fintype D]

variable (e : A → ScalarSiteExpansion S) (selected : A → D) (scale : A → ℝ)

noncomputable def scaledSiteFamilyFactor (k : ∀ a, (e a).Term) (s : S)
    (r : ∀ a, ZMod ((e a).period (k a))) (x : D → ℝ) : ℂ :=
  siteFamilyFactor e k s r (scaledSiteCoordinates selected scale x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FixedPrincipalCoefficientSpectrum
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def positiveModerateSpectrumConstant (n j : ℕ) (U V : ℝ) : ℝ :=
  (195 * positiveModerateCoverConstant n j U V ^ 4) ^ j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.BufferedScalarScoreBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def bufferedScalarScore {Ω : Type*} {m : ℕ}
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ) (T : Ω → (Fin m → ℤ) → ℝ)
    (f : Ω → ℝ) (lam : ℝ) (u : Ω) : ℝ :=
  (f u - lam) * χ.value (fun i => x u i - (nearestIntegerLift (x u) i : ℝ)) *
    T u (nearestIntegerLift (x u))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FixedListPowerBudget
namespace OAI

section

namespace Erdos3

noncomputable def fixedListBudgetPolynomial (B c : ℕ) : Polynomial ℕ :=
  let X := Polynomial.X
  let q := Polynomial.C 10 * (X + (X + 2) ^ B + 2)
  let R := (q + 2) ^ c
  let S := R + (R + 2) ^ 2 + 3
  R + ((S + 2) ^ 2 + S + (S + (S ^ 2 + S + 3) ^ 2) + S ^ 2 + 4)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedEndpointIdentity
namespace OAI

section

namespace Erdos3

open MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

variable {D G E : Type*} [Fintype D] [Fintype G] [Fintype E]
variable {B : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (axis : E → D)

local notation "Output" => (Σ _e : E, Unit)

noncomputable def jointSlicedProfilePrincipal
    (γ : D → ℝ) (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ)
    (e : E) (b : B (axis e)) : ℝ :=
  3 * γ (axis e) / 2 + γ (axis e) / 2 * r e (principalCoefficientSlot h (axis e) b)

noncomputable def jointSlicedProfileShift
    (ρ : D → ℝ) (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ) (o : Output) : ℝ :=
  ρ (axis o.1) * r o.1 (constantCoefficientSlot _ _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCenteredJointSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

noncomputable def allocatedTupleSpatialError {I J : Type*} [Fintype I] [Fintype J]
    (n : ℕ) (selection : I ↪ J) (N : Type*) [Fintype N] (M period : ℕ)
    (Czero rho xi W delta mesh : ℝ) : ℝ :=
  let gamma := (period : ℝ) ^ Fintype.card (Unit ⊕ I)
  let K := anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * (1 + W)
  let Eone := anisotropicSpatialError selection N M (1 / (M : ℝ)) Czero rho xi + gamma * K * delta
  (n : ℝ) * (Eone + 4 * gamma * K * mesh) *
    (1 + gamma * anisotropicSpatialDensityCap selection (1 / (M : ℝ)) + Eone) ^ n

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedModularCanonicalDetectorResourceBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedModularCanonicalDetectorResources {α : Type*} [Semiring α]
    (K : PreparedModularCanonicalDetectorResourceConstants) (P : α) :
    PreparedModularCanonicalDetectorResources α :=
  let Q : α := (P + K.Cperiod) ^ K.Cperiod
  let v : α := P + 8
  let w : α := P + 1
  let Dg : α := 2 * P + K.m * P + (layerTailDegree K.m + 1 : ℕ) + K.m + comparisonProfileBound + 8
  let Pproj : α := 4 * (P + 8) ^ 2
  let coverLog : α := (Pproj + 3 + K.Acover) ^ K.Acover
  let Pmass : α := (Pproj + K.Asample) ^ K.Asample
  let Vlog : α := P ^ 2 * ((layerTailDegree K.m + 1 : ℕ) * P + 1)
  let Nlog : α := (2 * K.m : ℕ) * (2 * P + 16) * (1 + 4 * (2 * P + 8))
  let Pbox : α := 2 * P + 8
  let Banalytic : α := Dg + 4 * P + 32
  let baseAmbient : α := Pproj + coverLog + Vlog + Nlog + Q + (layerTailDegree K.m + 1 : ℕ) * P + 3 * P + comparisonProfileBound + 32
  let tq : α := 1 + Q + (P + 1) + 1
  let pq : α := K.Cgrid + 2 * Q + (P + 1) + 4
  let gridlog : α := slicedGridGeometryLog Dg v w tq + pq
  let Fpref : α := (P + K.Cpref) ^ K.Cpref
  let sumlog : α := Pbox + P + Vlog + Nlog + Q + P
  let idealQ : α := 1 + P * sumlog + (P + comparisonProfileBound + (P + 1) * sumlog) + sumlog + 1
  let ambient : α := affineAmbientPrimitiveBudget baseAmbient idealQ
  let Psample : α := Pmass + ambient + Pproj + 2 * P + K.m * (K.m + 2 : ℕ) + 8
  let Pside : α := Psample + Pproj + Pmass + 2 * P
  let Pnative : α := Dg + gridlog + v + Fpref + 6 * P + Banalytic
  let nativeBudget : α := ((Pnative + K.Cnative) ^ K.Cnative + K.Anorm) ^ K.Anorm
  let E : α := 3 * P + nativeBudget + 30
  let full : α := 4 * (P + 8) ^ 2
  let required : α := (Psample + K.Apert) ^ K.Apert + (Pmass + K.AmassWindow) ^ K.AmassWindow + (Pproj + K.Aproj) ^ K.Aproj + (Pside + K.Aside) ^ K.Aside + (full + E + K.Amarginal) ^ K.Amarginal
  { Q, v, w, Dg, Pproj, coverLog, Pmass, Vlog, Nlog, Pbox, Banalytic, baseAmbient, tq, pq, gridlog, Fpref, sumlog, idealQ, ambient, Psample, Pside, Pnative, nativeBudget, E, full, required }

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.OriginalKernelResidueRetained
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {K T γ : ℝ} (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
variable (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))
variable (q : ℕ) (hq : 0 < q) (r : ZMod q)

open scoped Classical

theorem scalarCubeResidueSet_empty_eq_filter (L q : ℕ) (r : ZMod q) :
    scalarCubeResidueSet Empty L (fun _ => q) (fun _ => r) =
      Finset.univ.filter (fun z : IntegerScalarCubeBox Empty L => ((z none : ℤ) : ZMod q) = r) := by
  ext z
  simp only [mem_scalarCubeResidueSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun h => h none
  · intro h i
    cases i with
    | none => exact h
    | some e => exact e.elim

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastContinuousRetainedExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

universe u v w uR

variable {R : Type uR} {A : Type u} {S : Type v}
variable [Fintype R] [Fintype A] [Fintype S]
variable (e : R → A → ScalarSiteExpansion.{v,w} S)

noncomputable def forecastSiteMixtureCoefficient (c : R → ℂ)
    (t : Σ r, ∀ a, (e r a).Term) : ℂ :=
  c t.1 * siteFamilyCoefficient (e t.1) t.2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.MonomialCharacterMean
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[simp]
theorem norm_euclideanCharacter (ξ x : E) : ‖euclideanCharacter ξ x‖ = 1 := by
  simp [euclideanCharacter]

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def monomialCharacterMean (k : ℕ) (α : E) (N : ℕ) (ξ : E) : ℂ :=
  (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), euclideanCharacter ξ ((n : ℝ) ^ k • α)) /
    ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℂ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeDualCoordinates
namespace OAI

section

namespace Erdos3

open Module

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

noncomputable def latticeDualPoint (b : Basis ι ℤ Λ) (n : ι → ℤ) : E :=
  (latticeDualBasis Λ b).equivFun.symm (fun i => (n i : ℝ))

@[simp]
theorem latticeDualPoint_neg (b : Basis ι ℤ Λ) (n : ι → ℤ) :
    latticeDualPoint Λ b (-n) = -latticeDualPoint Λ b n := by
  simp only [latticeDualPoint, Pi.neg_apply, Int.cast_neg]
  change (latticeDualBasis Λ b).equivFun.symm (-(fun i => (n i : ℝ))) = _
  exact map_neg _ _

theorem latticeDualPoint_mem (b : Basis ι ℤ Λ) (n : ι → ℤ) :
    latticeDualPoint Λ b n ∈ euclideanDualLattice Λ := by
  rw [euclideanDualLattice_eq_span Λ b, (latticeDualBasis Λ b).mem_span_iff_repr_mem ℤ]
  intro i
  refine ⟨n i, ?_⟩
  have h := congrFun ((latticeDualBasis Λ b).equivFun.apply_symm_apply (fun j => (n j : ℝ))) i
  exact h.symm

theorem latticeDualPoint_injective (b : Basis ι ℤ Λ) : Function.Injective (latticeDualPoint Λ b) := by
  intro n m h
  have he := congrArg (latticeDualBasis Λ b).equivFun h
  simp only [latticeDualPoint, LinearEquiv.apply_symm_apply] at he
  ext i
  exact Int.cast_injective (congrFun he i)

theorem latticeDualPoint_surjective (b : Basis ι ℤ Λ) (ξ : euclideanDualLattice Λ) :
    ∃ n : ι → ℤ, latticeDualPoint Λ b n = ξ := by
  classical
  have hmem := ((latticeDualBasis Λ b).mem_span_iff_repr_mem ℤ (ξ : E)).mp
    ((euclideanDualLattice_eq_span Λ b).le ξ.property)
  choose n hn using hmem
  refine ⟨n, ?_⟩
  apply (latticeDualBasis Λ b).equivFun.injective
  ext i
  change (latticeDualBasis Λ b).equivFun
    ((latticeDualBasis Λ b).equivFun.symm (fun j => (n j : ℝ))) i = _
  rw [LinearEquiv.apply_symm_apply]
  exact hn i

noncomputable def latticeDualEquiv (b : Basis ι ℤ Λ) : (ι → ℤ) ≃ euclideanDualLattice Λ :=
  Equiv.ofBijective (fun n => ⟨latticeDualPoint Λ b n, latticeDualPoint_mem Λ b n⟩)
    ⟨fun _ _ h => latticeDualPoint_injective Λ b (congrArg Subtype.val h), fun ξ => by
      obtain ⟨n, hn⟩ := latticeDualPoint_surjective Λ b ξ
      exact ⟨n, Subtype.ext hn⟩⟩

@[simp]
theorem latticeDualEquiv_coe (b : Basis ι ℤ Λ) (n : ι → ℤ) :
    ((latticeDualEquiv Λ b n : euclideanDualLattice Λ) : E) = latticeDualPoint Λ b n := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.LatticeTorusFourierCoefficient
namespace OAI

section

namespace Erdos3

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

noncomputable def latticeGaussianTorus (b : Module.Basis ι ℤ Λ) {t : ℝ} (ht : 0 < t) :
    C(UnitAddTorus ι, ℂ) where
  toFun := integerPeriodicTorusLift (fun x =>
    (latticeGaussianMass Λ t ((b.ofZLatticeBasis ℝ Λ).equivFun.symm x) : ℂ))
  continuous_toFun := continuous_integerPeriodicTorusLift _
    (Complex.continuous_ofReal.comp ((continuous_latticeGaussianMass Λ ht).comp
      (b.ofZLatticeBasis ℝ Λ).equivFunL.symm.continuous))
    (fun x n => congrArg (fun z : ℝ => (z : ℂ)) (latticeGaussian_integer_periodic Λ b t x n))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteUniformCoordinateRefresh
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I J X : Type*}

noncomputable def coordinateResamplingEquiv (f : J → I) (hf : Function.Injective f) :
    ((I → X) × (J → X)) ≃ ((I → X) × (J → X)) where
  toFun p := (Function.extend f p.2 p.1, p.1 ∘ f)
  invFun p := (Function.extend f p.2 p.1, p.1 ∘ f)
  left_inv p := by
    apply Prod.ext
    · funext i
      by_cases hi : i ∈ Set.range f
      · obtain ⟨j, rfl⟩ := hi
        exact hf.extend_apply _ _ j
      · change Function.extend f (p.1 ∘ f) (Function.extend f p.2 p.1) i = p.1 i
        rw [Function.extend_apply' _ _ _ hi, Function.extend_apply' _ _ _ hi]
    · funext j
      exact hf.extend_apply _ _ j
  right_inv p := by
    apply Prod.ext
    · funext i
      by_cases hi : i ∈ Set.range f
      · obtain ⟨j, rfl⟩ := hi
        exact hf.extend_apply _ _ j
      · change Function.extend f (p.1 ∘ f) (Function.extend f p.2 p.1) i = p.1 i
        rw [Function.extend_apply' _ _ _ hi, Function.extend_apply' _ _ _ hi]
    · funext j
      exact hf.extend_apply _ _ j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairUniformFactors
namespace OAI

universe u

section

namespace Erdos3

namespace VectorPolynomial

open RationalFilteredNilmanifold

theorem allocatedFrozenTaggedPairBudget_mono (s C A : ℕ)
    {pGeo pGeo' p p' : ℝ} (hGeo0 : 0 ≤ pGeo) (hp0 : 0 ≤ p)
    (hGeo : pGeo ≤ pGeo') (hp : p ≤ p') :
    allocatedFrozenTaggedPairBudget s C A pGeo p ≤
      allocatedFrozenTaggedPairBudget s C A pGeo' p' := by
  unfold allocatedFrozenTaggedPairBudget fixedAdaptedSymbolTransferInput
  gcongr

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

def candidateFrontFactorScalarConclusion (s : ℕ)
    (p actualGeometry cost terminal commonInput fast longThreshold
      aProjected aCommon aMarkInput common aAdapted aMarkBudget aJointGeo initialShort : ℝ) : Prop :=
  terminal ∈ Set.Icc 0 commonInput ∧
    allocatedCandidateCommonFastBudget s terminal ≤ fast ∧
    max cost initialShort ≤ longThreshold ∧
    (aProjected + 2) ^ 3 + aCommon ≤ commonInput ∧
    aMarkInput ∈ Set.Icc 0 commonInput ∧
    aCommon ∈ Set.Icc 0 common ∧
    p ≤ commonInput ∧ actualGeometry ≤ commonInput ∧
    aAdapted ≤ commonInput ∧ aMarkBudget ≤ commonInput ∧
    aJointGeo ≤ commonInput ∧ (aProjected + 2) ^ 4 ≤ commonInput ∧ cost ≤ commonInput

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CandidateFrontActualPowerBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open RationalFilteredNilmanifold

attribute [local irreducible] candidateFrontFactorScalarConclusion

theorem candidateFrontFactor_actual_bounds
    (s Cgeometry Cpair Cbasis K T Cmark : ℕ)
    {p factor geom actualFactor actualGeometry cost nVariables : ℝ}
    (hp : 0 ≤ p) (hfactor : 0 ≤ actualFactor) (hgeometry : 0 ≤ actualGeometry)
    (hfactor_le : actualFactor ≤ factor) (hgeometry_le : actualGeometry ≤ geom)
    (hcost : cost ≤ p) (hvariables0 : 0 ≤ nVariables) (hvariables : nVariables ≤ p) :
    let pairGeo : ℝ := (geom + 2) ^ 2
    let jointGeo : ℝ := (geom + 3) ^ 2
    let adapted : ℝ := (jointGeo + 2) ^ Cgeometry
    let bnd : ℝ := adapted + (pairGeo + 3) ^ 5 + pairGeo + jointGeo + geom + factor + 2
    let localCost : ℝ := allocatedFrozenTaggedPairBudget s Cpair Cbasis pairGeo factor
    let jointCost : ℝ := allocatedFrozenTaggedFamilyInputBudget bnd localCost
    let fullCost : ℝ := jointCost + (jointCost + K) ^ K
    let common : ℝ := (fullCost + 2) ^ T + (((fullCost + 2) ^ 2 + 2) ^ 63 + 1) + fullCost + 1
    let projected : ℝ := common + adapted + 1
    let markHeight : ℝ := quotientInducedMarkHeightBudget geom
    let markInput : ℝ := jointGeo + markHeight + adapted + 2
    let markBudget : ℝ := (markInput + 2) ^ Cmark
    let commonInput : ℝ := p + geom + pairGeo + jointGeo + jointGeo ^ 2 + adapted + bnd + factor +
      common + projected + (projected + 2) ^ 4 + markHeight + markInput + markBudget + 2
    let fast : ℝ := allocatedCandidateCommonFastBudget s commonInput
    let longThreshold : ℝ := (factor + 2 + Cpair) ^ Cpair + 7 * factor + 22 +
      (fullCost + 2) ^ T + p + 1
    let aPairGeo : ℝ := (actualGeometry + 2) ^ 2
    let aJointGeo : ℝ := (actualGeometry + 3) ^ 2
    let aAdapted : ℝ := (aJointGeo + 2) ^ Cgeometry
    let aBnd : ℝ := aAdapted + (aPairGeo + 3) ^ 5 + aPairGeo + aJointGeo +
      actualGeometry + actualFactor + 2
    let aLocalCost : ℝ := allocatedFrozenTaggedPairBudget s Cpair Cbasis aPairGeo actualFactor
    let aJointCost : ℝ := allocatedFrozenTaggedFamilyInputBudget aBnd aLocalCost
    let aFullCost : ℝ := aJointCost + (aJointCost + K) ^ K
    let aCommon : ℝ := (aFullCost + 2) ^ T + (((aFullCost + 2) ^ 2 + 2) ^ 63 + 1) + aFullCost + 1
    let aProjected : ℝ := max aCommon 0 + aAdapted + 1
    let aMarkInput : ℝ := nativeOptionFixedSourceQuotientMarkInput actualGeometry
    let aMarkBudget : ℝ := (aMarkInput + 2) ^ Cmark
    let terminal : ℝ := (aProjected + 2) ^ 4 + aMarkInput + aMarkBudget + aJointGeo + nVariables + 2
    let initialShort : ℝ := max ((actualFactor + 2 + Cpair) ^ Cpair + 7 * actualFactor + 22)
      ((aFullCost + 2) ^ T)
    candidateFrontFactorScalarConclusion s p actualGeometry cost terminal commonInput fast
      longThreshold aProjected aCommon aMarkInput common aAdapted aMarkBudget aJointGeo initialShort := by
  intro pg jg ad bd lc jc fc co pr mh mi mb ci fa lt
    apg ajg aad abd alc ajc afc aco apr ami amb terminal initialShort
  unfold candidateFrontFactorScalarConclusion
  have hf : 0 ≤ factor := hfactor.trans hfactor_le
  have hg : 0 ≤ geom := hgeometry.trans hgeometry_le
  have hpg0 : 0 ≤ pg := by dsimp only [pg]; positivity
  have hjg0 : 0 ≤ jg := by dsimp only [jg]; positivity
  have had0 : 0 ≤ ad := by dsimp only [ad]; positivity
  have hbpow0 : 0 ≤ (pg + 3) ^ 5 := by positivity
  have hbd0 : 0 ≤ bd := by dsimp only [bd]; positivity
  have hlc0 : 0 ≤ lc := by
    dsimp only [lc, allocatedFrozenTaggedPairBudget, fixedAdaptedSymbolTransferInput]
    positivity
  have hjc0 : 0 ≤ jc := by dsimp only [jc, allocatedFrozenTaggedFamilyInputBudget]; positivity
  have hfc0 : 0 ≤ fc := by dsimp only [fc]; positivity
  have hco0 : 0 ≤ co := by dsimp only [co]; positivity
  have hpr0 : 0 ≤ pr := by dsimp only [pr]; positivity
  have hmh0 : 0 ≤ mh := by dsimp only [mh, quotientInducedMarkHeightBudget]; positivity
  have hmi0 : 0 ≤ mi := by dsimp only [mi]; positivity
  have hmb0 : 0 ≤ mb := by dsimp only [mb]; positivity
  have hjgSq0 : 0 ≤ jg ^ 2 := sq_nonneg _
  have hprPow0 : 0 ≤ (pr + 2) ^ 4 := by positivity
  have hapg0 : 0 ≤ apg := by dsimp only [apg]; positivity
  have hajg0 : 0 ≤ ajg := by dsimp only [ajg]; positivity
  have haad0 : 0 ≤ aad := by dsimp only [aad]; positivity
  have habd0 : 0 ≤ abd := by dsimp only [abd]; positivity
  have halc0 : 0 ≤ alc := by
    dsimp only [alc, allocatedFrozenTaggedPairBudget, fixedAdaptedSymbolTransferInput]
    positivity
  have hajc0 : 0 ≤ ajc := by dsimp only [ajc, allocatedFrozenTaggedFamilyInputBudget]; positivity
  have hafc0 : 0 ≤ afc := by dsimp only [afc]; positivity
  have haco0 : 0 ≤ aco := by dsimp only [aco]; positivity
  have hapr0 : 0 ≤ apr := by dsimp only [apr]; positivity
  have hami0 : 0 ≤ ami := (nativeOptionFixedSourceQuotientMarkInput_bounds hgeometry).1
  have hamb0 : 0 ≤ amb := by dsimp only [amb]; positivity
  have hterminal0 : 0 ≤ terminal := by dsimp only [terminal]; positivity
  have hpg : apg ≤ pg := by dsimp only [apg, pg]; gcongr
  have hjg : ajg ≤ jg := by dsimp only [ajg, jg]; gcongr
  have had : aad ≤ ad := by dsimp only [aad, ad]; gcongr
  have hbd : abd ≤ bd := by dsimp only [abd, bd]; gcongr
  have hlc : alc ≤ lc :=
    allocatedFrozenTaggedPairBudget_mono s Cpair Cbasis hapg0 hfactor hpg hfactor_le
  have hjc : ajc ≤ jc := allocatedFrozenTaggedFamilyInputBudget_mono habd0 hbd hlc
  have hfc : afc ≤ fc := by dsimp only [afc, fc]; gcongr
  have hco : aco ≤ co := by dsimp only [aco, co]; gcongr
  have hpr : apr ≤ pr := by
    dsimp only [apr, pr]
    rw [max_eq_left haco0]
    exact add_le_add (add_le_add hco had) le_rfl
  have hmh : quotientInducedMarkHeightBudget actualGeometry ≤ mh :=
    quotientInducedMarkHeightBudget_mono hgeometry hgeometry_le
  have hmi : ami ≤ mi := by
    dsimp only [ami, nativeOptionFixedSourceQuotientMarkInput, mi]
    change ajg + quotientInducedMarkHeightBudget actualGeometry ≤ jg + mh + ad + 2
    linarith only [hjg, hmh, had0]
  have hmb : amb ≤ mb := by dsimp only [amb, mb]; gcongr
  have hpow4 : (apr + 2) ^ 4 ≤ (pr + 2) ^ 4 := by gcongr
  clear_value pg jg ad bd lc jc fc co pr mh mi mb apg ajg aad abd alc ajc afc aco apr ami amb
  have hterminal : terminal ≤ ci := by
    dsimp only [terminal, ci]
    linarith only [hpow4, hmi, hmb, hjg, hvariables, hp, hg, hpg0, hjg0, hjgSq0,
      had0, hbd0, hf, hco0, hpr0, hmh0]
  have hmi_ci : mi ≤ ci := by
    dsimp only [ci]
    linarith only [hp, hg, hpg0, hjg0, hjgSq0, had0, hbd0, hf, hco0,
      hpr0, hprPow0, hmh0, hmb0]
  have hnative : (apr + 2) ^ 3 + aco ≤ ci := by
    have hpow3base : (apr + 2) ^ 3 ≤ (pr + 2) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (add_le_add hpr (le_refl 2)) 3
    have hpow3 : (apr + 2) ^ 3 ≤ (pr + 2) ^ 4 :=
      hpow3base.trans (pow_le_pow_right₀
        (by linarith only [hpr0] : 1 ≤ pr + 2) (by decide : 3 ≤ 4))
    dsimp only [ci]
    linarith only [hpow3, hco, hp, hg, hpg0, hjg0, hjgSq0, had0, hbd0,
      hf, hpr0, hmh0, hmi0, hmb0]
  have hlong : max cost initialShort ≤ lt := by
    have hpair : (actualFactor + 2 + Cpair) ^ Cpair + 7 * actualFactor + 22 ≤
        (factor + 2 + Cpair) ^ Cpair + 7 * factor + 22 := by gcongr
    have hfull : (afc + 2) ^ T ≤ (fc + 2) ^ T := by gcongr
    have hpair0 : 0 ≤ (factor + 2 + Cpair) ^ Cpair + 7 * factor + 22 := by positivity
    have hfull0 : 0 ≤ (fc + 2) ^ T := by positivity
    dsimp only [lt, initialShort]
    apply max_le
    · linarith only [hcost, hpair0, hfull0]
    · apply max_le <;> linarith only [hpair, hfull, hpair0, hfull0, hp]
  have hp_ci : p ≤ ci := by
    dsimp only [ci]
    linarith only [hg, hpg0, hjg0, hjgSq0, had0, hbd0, hf, hco0,
      hpr0, hprPow0, hmh0, hmi0, hmb0]
  have hg_ci : geom ≤ ci := by
    dsimp only [ci]
    linarith only [hp, hpg0, hjg0, hjgSq0, had0, hbd0, hf, hco0,
      hpr0, hprPow0, hmh0, hmi0, hmb0]
  have had_ci : ad ≤ ci := by
    dsimp only [ci]
    linarith only [hp, hg, hpg0, hjg0, hjgSq0, hbd0, hf, hco0,
      hpr0, hprPow0, hmh0, hmi0, hmb0]
  have haprPow0 : 0 ≤ (apr + 2) ^ 4 := by positivity
  have hambTerminal : amb ≤ terminal := by
    dsimp only [terminal]
    linarith only [haprPow0, hami0, hajg0, hvariables0]
  have hajgTerminal : ajg ≤ terminal := by
    dsimp only [terminal]
    linarith only [haprPow0, hami0, hamb0, hvariables0]
  have haprTerminal : (apr + 2) ^ 4 ≤ terminal := by
    dsimp only [terminal]
    linarith only [hami0, hamb0, hajg0, hvariables0]
  exact ⟨⟨hterminal0, hterminal⟩,
    allocatedCandidateCommonFastBudget_mono s hterminal0 hterminal, hlong, hnative,
    ⟨hami0, hmi.trans hmi_ci⟩, ⟨haco0, hco⟩, hp_ci, hgeometry_le.trans hg_ci,
    had.trans had_ci, hambTerminal.trans hterminal, hajgTerminal.trans hterminal,
    haprTerminal.trans hterminal, hcost.trans hp_ci⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFiniteModelPhysicalExpansion
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

variable {m : ℕ} {O J : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

noncomputable def rowsAmbientSite
    (s : Finset α)
    (z : JetAmbientIndex (fun j => {t : Finset α // t ∈ rowSets j}) J → UnitAddCircle) :
    JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle :=
  fun a => ∑ t, rowRestrictedSiteMatrix (rowSets a.1) s t • z ⟨a.1, t, a.2.2⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedSpatialKernelSliceDensity
namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X] [Fintype T]
variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)

omit [Fintype G] [Fintype T] in
theorem fixedSpatialKernelBlockEquiv_coe (b : Bool)
    (h : (fixedSpatialKernelBlock e W L z b).det ≠ 0) :
    (fixedSpatialKernelBlockEquiv e W L z b h).toContinuousLinearMap =
      matrixSupCLM (fixedSpatialKernelBlock e W L z b) :=
  Classical.choose_spec (matrixSupCLM_inverse_spec (fixedSpatialKernelBlock e W L z b) h).1

omit [Fintype G] [Fintype T] in
theorem fixedSpatialKernelBlockEquiv_jacobian (b : Bool)
    (h : (fixedSpatialKernelBlock e W L z b).det ≠ 0) :
    inverseJacobian (fixedSpatialKernelBlockEquiv e W L z b h) =
      |(fixedSpatialKernelBlock e W L z b).det|⁻¹ := by
  rw [inverseJacobian_eq]
  congr 2
  change LinearMap.det (fixedSpatialKernelBlockEquiv e W L z b h).toContinuousLinearMap.toLinearMap = _
  rw [fixedSpatialKernelBlockEquiv_coe]
  exact LinearMap.det_toLin' _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedCenteredForecastSpatialBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical Matrix

variable {G J X : Type*}

theorem preparedCenteredForecast_spatialBlock_eq
    (e : Fin 2 × X ↪ G) (W L τ ξ : ℝ) (N : X → ℕ)
    (noise : Option (G ⊕ J) × X → ℤ) (t : Bool) :
    fixedSpatialKernelBlock (spatialTwoBlockEquiv e) W L
      (fun k => (noise (Option.map Sum.inl k.1, k.2) : ℝ) / trimmedSpatialWidths W τ N k) t =
      (L / (1 + W)) • (fun i j => spatialMatrixNormalizedEntries e
        (narrowTrimmedSpatialWidths W τ ξ N) noise ((if t then 1 else 0), j, i) : Matrix X X ℝ) := by
  cases t <;> rfl

theorem preparedCenteredForecast_spatialBlock_abs_det [Fintype X] [DecidableEq X]
    (e : Fin 2 × X ↪ G) (W L τ ξ : ℝ) (N : X → ℕ)
    (noise : Option (G ⊕ J) × X → ℤ) (t : Bool) (hscale : 0 ≤ L / (1 + W)) :
    |(fixedSpatialKernelBlock (spatialTwoBlockEquiv e) W L
      (fun k => (noise (Option.map Sum.inl k.1, k.2) : ℝ) / trimmedSpatialWidths W τ N k) t).det| =
      (L / (1 + W)) ^ Fintype.card X * |Matrix.det (fun i j => spatialMatrixNormalizedEntries e
        (narrowTrimmedSpatialWidths W τ ξ N) noise ((if t then 1 else 0), j, i))| := by
  let A : Matrix X X ℝ := fun i j => spatialMatrixNormalizedEntries e
    (narrowTrimmedSpatialWidths W τ ξ N) noise ((if t then 1 else 0), j, i)
  have heq : fixedSpatialKernelBlock (spatialTwoBlockEquiv e) W L
      (fun k => (noise (Option.map Sum.inl k.1, k.2) : ℝ) / trimmedSpatialWidths W τ N k) t =
      (L / (1 + W)) • A := preparedCenteredForecast_spatialBlock_eq e W L τ ξ N noise t
  calc
    _ = |((L / (1 + W)) • A).det| := congrArg (fun M : Matrix X X ℝ => |M.det|) heq
    _ = (L / (1 + W)) ^ Fintype.card X * |A.det| := by
      rw [Matrix.det_smul, abs_mul, abs_of_nonneg (pow_nonneg hscale _)]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFinalScalarPowerBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

def preparedFinalScalarBudget (m degree : ℕ) (t : ℝ) : ℝ :=
  2048 * t ^ 3 + (t + 2) ^ (preparedIntegralBasisExponent m + 1) +
    2 * t + 1 + degree * t

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedEndpointPerturbationPolynomial
namespace OAI

section

namespace Erdos3

theorem exists_preparedEndpointPerturbation_budget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {t D primitiveCap Ptest Ecompare cost : ℝ},
      0 ≤ t → D ∈ Set.Icc 0 t → primitiveCap ∈ Set.Icc 0 t →
      Ptest ∈ Set.Icc 0 t → Ecompare ∈ Set.Icc 0 t → cost ∈ Set.Icc 0 t →
      let sourceLog := 2 + D ^ 2 + primitiveCap + max 0 Ptest
      fixedPathSlicedPerturbationLog D (D + sourceLog + 4) (cost + 1)
          (2 * sourceLog + Ecompare + 18) m ∈ Set.Icc 0 ((t + C) ^ C) ∧
        2 * sourceLog + Ecompare + 18 ∈ Set.Icc 0 ((t + C) ^ C) := by
  let Lpoly : Polynomial ℕ := 2 + Polynomial.X ^ 2 + 2 * Polynomial.X
  let Epoly : Polynomial ℕ := 2 * Lpoly + Polynomial.X + 18
  let Qpoly : Polynomial ℕ := 4 * Polynomial.X + 3 * Lpoly + Polynomial.C m + 25
  let Tpoly : Polynomial ℕ :=
    48 * ((3 * Qpoly + 4) * Polynomial.C m + 5 * Qpoly + 10) +
      2 * Qpoly + 2 * Polynomial.C m + 47
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (Tpoly + Epoly)
  refine ⟨C, hC, ?_⟩
  intro t D primitiveCap Ptest Ecompare cost ht hD hprimitive htest hcompare hcost
  let sourceLog := 2 + D ^ 2 + primitiveCap + max 0 Ptest
  let L := 2 + t ^ 2 + 2 * t
  let E := 2 * L + t + 18
  let Q := 4 * t + 3 * L + m + 25
  let T := 48 * ((3 * Q + 4) * m + 5 * Q + 10) + 2 * Q + 2 * m + 47
  have hsource : 0 ≤ sourceLog := by
    dsimp only [sourceLog]
    exact add_nonneg (add_nonneg (by positivity) hprimitive.1) (le_max_left _ _)
  have hsourceL : sourceLog ≤ L := by
    have hsquare := pow_le_pow_left₀ hD.1 hD.2 2
    dsimp only [sourceLog, L]
    rw [max_eq_right htest.1]
    linarith only [hsquare, hprimitive.2, htest.2]
  have hE : 0 ≤ E := by dsimp only [E, L]; positivity
  have hT : 0 ≤ T := by dsimp only [T, Q, L]; positivity
  have hcoarse : 0 ≤ 2 * sourceLog + Ecompare + 18 := by
    linarith only [hsource, hcompare.1]
  have hcoarseE : 2 * sourceLog + Ecompare + 18 ≤ E := by
    dsimp only [E]
    linarith only [hsourceL, hcompare.2]
  have hQ : D + ((D + sourceLog + 4) + (cost + 1)) +
      (2 * sourceLog + Ecompare + 18) + m + 2 ≤ Q := by
    dsimp only [Q]
    linarith only [hsourceL, hD.2, hcost.2, hcompare.2]
  have hQm := mul_le_mul_of_nonneg_right hQ (Nat.cast_nonneg (α := ℝ) m)
  have hperturb : fixedPathSlicedPerturbationLog D (D + sourceLog + 4) (cost + 1)
      (2 * sourceLog + Ecompare + 18) m ≤ T := by
    dsimp only [fixedPathSlicedPerturbationLog, fixedPathPerturbationLog, T]
    nlinarith only [hQ, hQm]
  have htotal : T + E ≤ (t + C) ^ C := by
    simpa [Tpoly, Epoly, Qpoly, Lpoly, T, Q, E, L] using hbound t ht
  exact ⟨⟨fixedPathSlicedPerturbationLog_nonneg hD.1
      (by linarith only [hD.1, hsource]) (by linarith only [hcost.1]) hcoarse m,
      hperturb.trans ((le_add_of_nonneg_right hE).trans htotal)⟩,
    ⟨hcoarse, hcoarseE.trans ((le_add_of_nonneg_left hT).trans htotal)⟩⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedRelativeEndpointComparisonBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedRelativeEndpointPerturbationLog_budget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {t D primitiveCap Ptest Ecompare cost : ℝ},
      0 ≤ t → D ∈ Set.Icc 0 t → primitiveCap ∈ Set.Icc 0 t →
      Ptest ∈ Set.Icc 0 t → Ecompare ∈ Set.Icc 0 t → cost ∈ Set.Icc 0 t →
      preparedRelativeEndpointSigmaLog D primitiveCap Ptest Ecompare cost m ∈
        Set.Icc 0 ((t + C) ^ C) ∧
      preparedRelativeEndpointCoarseLog D primitiveCap Ptest Ecompare ∈
        Set.Icc 0 ((t + C) ^ C) := by
  obtain ⟨C, hC, hbound⟩ := exists_preparedEndpointPerturbation_budget m
  refine ⟨C, hC, ?_⟩
  intro t D primitiveCap Ptest Ecompare cost ht hD hcap htest hcompare hcost
  exact hbound ht hD hcap htest hcompare hcost

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCubeMinorGoodMass
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def affineCubeMinorThreshold (J O α : Type*) [Fintype J] [Fintype O] [Fintype α]
    [DecidableEq α] (h N d : ℕ) (c₀ δ η : ℝ) : ℝ :=
  polynomialSublevelThreshold (N * d) (Fintype.card J)
    (cubeMinorProbabilityConstant O α h N d * δ⁻¹ ^ N)
    (cubeMinorProbabilityScale O N d c₀) η

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

variable {B O J α : Type*} [Fintype B] [Fintype O] [Fintype J] [Fintype α]
  [DecidableEq B] [DecidableEq O] [DecidableEq α] {h : ℕ}

noncomputable def affineBooleanCubeDeterminant
    (c : B → ℝ) (sets : O → Finset α) (block : O → B)
    (v : Fin h) (sel : O → Option α)
    (L : (BlockParameter B (Fin h) α → ℝ) →L[ℝ] (BlockParameter B (Fin h) α → ℝ))
    (b : BlockParameter B (Fin h) α → ℝ) (x : (B × Fin h) → Option α → ℝ) : ℝ :=
  booleanMinorDeterminant c sets block v sel (b + L (blockCubeFlatten B (Fin h) α x))

noncomputable def affineBooleanCubeCutoff
    (c : J → B → ℝ) (sets : O → Finset α) (block : J → O → B)
    (v : Fin h) (sel : J → O → Option α)
    (L : (BlockParameter B (Fin h) α → ℝ) →L[ℝ] (BlockParameter B (Fin h) α → ℝ))
    (b : BlockParameter B (Fin h) α → ℝ)
    (ψ : ℝ → ℝ) (r : B × Fin h → ℝ) (κ : J → ℝ)
    (a : BlockParameter B (Fin h) α → ℝ) : ℝ :=
  goodDomainCutoff ψ κ
    (fun j => affineBooleanCubeDeterminant (c j) sets (block j) v (sel j) L b)
    (scalarCubeProductCutoff α r) ((blockCubeFlatten B (Fin h) α).symm a)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineBooleanCubeComparison
namespace OAI

section

namespace Erdos3

open scoped ContDiff

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [decidableEqB : ∀ d, DecidableEq (B d)] [decidableEqO : ∀ d, DecidableEq (O d)] {h : D → ℕ}

noncomputable def jointAffineBooleanSampler (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) ≃L[ℝ]
      (BlockParameter (B d) (Fin (h d)) α → ℝ))
    (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ) :
    (JointBlockParameter B h α → ℝ) → ((Σ d, O d) → ℝ) :=
  sigmaAxisSampler (fun d x => booleanSamplerMap (c d) (sets d) (b d + L d x))

noncomputable def jointAffineBooleanInjection
    (block : ∀ d, O d → B d) (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
    (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) ≃L[ℝ]
      (BlockParameter (B d) (Fin (h d)) α → ℝ)) (δ : D → ℝ) :
    ((Σ d, O d) → ℝ) →L[ℝ] (JointBlockParameter B h α → ℝ) :=
  sigmaAxisOperator (fun d => affineSelectedInjection (L d)
    (booleanSelectedInjection (block d) (v d) (sel d)) (δ d))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.JointAffineBooleanSource
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}
  (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
  (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
  (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) →L[ℝ]
    (BlockParameter (B d) (Fin (h d)) α → ℝ))
  (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
  (ψ : ℝ → ℝ) (r : ∀ d, B d × Fin (h d) → ℝ) (κ : D → ℝ)

noncomputable def jointAffineBooleanCutoff : (JointBlockParameter B h α → ℝ) → ℝ :=
  sigmaAxisWeight (fun d => affineBooleanCubeCutoff (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d))

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}

noncomputable def jointAffineBooleanTranslationBudget
    (C : D → ℝ) (A T : ℝ≥0) (r : ∀ d, B d × Fin (h d) → ℝ)
    (κ : D → ℝ) (K H : ℝ≥0) : ℝ≥0 :=
  (Fintype.card (Σ d, O d) : ℝ≥0) *
    (K * Real.toNNReal (jointBooleanWeightBudget (O := O) (α := α) h C A T r κ) +
      (Fintype.card (JointBlockParameter B h α) : ℝ≥0) * (K ^ 2 * H))

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

noncomputable def canonicalAffineCubeMinorThreshold (O α : Type*) [Fintype O] [Fintype α]
    [DecidableEq α] (h : ℕ) (c₀ δ η : ℝ) : ℝ :=
  affineCubeMinorThreshold Unit O α h (cubeMinorVariableCount O α h) (cubeMinorDegree O h) c₀ δ η

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.JointAffineBooleanTolerance
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

noncomputable def jointAffineSourceBoundaryRadius (h : D → ℕ) (E : ℝ)
    (d : D) (_ : B d × Fin (h d)) : ℝ :=
  scalarCubeProductBoundaryRadius (B d × Fin (h d)) α
    ((E / (12 * ((Fintype.card D : ℝ) + 1))) / 2)

noncomputable def jointAffineSourceMinorThreshold (h : D → ℕ) (c₀ : D → ℝ) (δ E : ℝ)
    (d : D) : ℝ :=
  canonicalAffineCubeMinorThreshold (O d) α (h d) (c₀ d) δ
    (E / (12 * ((Fintype.card D : ℝ) + 1)))

noncomputable def jointAffineSourceRadius (h : D → ℕ) (c₀ C : D → ℝ)
    (A T : ℝ≥0) (δ E : ℝ) : ℝ :=
  let r := jointAffineSourceBoundaryRadius (B := B) (α := α) h E
  let κ := jointAffineSourceMinorThreshold (O := O) (α := α) h c₀ δ E
  let K := jointAffineBooleanInverseBudget (O := O) (α := α) h C κ δ
  let H := jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C
  let L := jointAffineBooleanTranslationBudget (O := O) (α := α) C A T r κ K H
  min 1 (E / (3 * (1 + (L : ℝ))))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PartitionedAffineLogEnvelope
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def affineBooleanAxisWeightCost (B O α : Type*) [Fintype B] [Fintype O]
    [Fintype α] [DecidableEq α] (h : ℕ) (C : ℝ) (A T : ℝ≥0) (c₀ δ η : ℝ) : ℝ :=
  (∑ _i : B × Fin h, ((2*2^Fintype.card α : ℕ) : ℝ)*((Fintype.card α : ℝ)+1)^2*T/
    scalarCubeProductBoundaryRadius (B × Fin h) α (η/2))+
  (Fintype.card (BlockParameter B (Fin h) α) : ℝ)*
    ((A : ℝ)/canonicalAffineCubeMinorThreshold O α h c₀ δ η*
      productMinorDeterminantDerivativeBound (Fintype.card (BlockParameter B (Fin h) α))
        (Fintype.card O) (Fintype.card α) h C 1)

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

noncomputable def canonicalSublevelCutoff : ℝ → ℝ :=
  Classical.choose (Classical.choose_spec exists_smooth_sublevel_cutoff).2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeEndpointNumericalBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedRelativeEndpointPerturbationExponent (m : ℕ) : ℕ :=
  (exists_preparedRelativeEndpointPerturbationLog_budget m).choose

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeCoordinateCells
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mem_primeCoordinateCell_anchor {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (q : ι → ℕ)
    (hcop : Pairwise (fun i j => (q i).Coprime (q j))) (I : Finset ι) (u z : σ → ℤ) :
    z ∈ primeCoordinateCell lo N q I (fun i j => (u j : ZMod (q i))) ↔
      z ∈ translatedIntegerBox lo N ∧ ∀ j, z j ≡ u j [ZMOD ((∏ i ∈ I, q i : ℕ) : ℤ)] := by
  rw [mem_primeCoordinateCell]
  constructor
  · rintro ⟨hz, heq⟩
    refine ⟨hz, ?_⟩
    intro j
    apply (modEq_selected_prod_iff q hcop I (z j) (u j)).mpr
    intro i hi
    exact (ZMod.intCast_eq_intCast_iff (z j) (u j) (q i)).mp (congrFun (heq i hi) j)
  · rintro ⟨hz, hmod⟩
    refine ⟨hz, ?_⟩
    intro i hi
    funext j
    exact (ZMod.intCast_eq_intCast_iff (z j) (u j) (q i)).mpr
      ((modEq_selected_prod_iff q hcop I (z j) (u j)).mp (hmod j) i hi)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ConcreteAffineMeshBoundary
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def integerBoxMeshPoint (lo hi : I → ℤ) (z : ∀ i, Finset.Ico (lo i) (hi i)) :
    translatedIntegerBox lo (fun i => (hi i - lo i).toNat) := by
  refine ⟨fun i => (z i : ℤ), (mem_translatedIntegerBox _ _ _).mpr ?_⟩
  intro i
  have h := Finset.mem_Ico.mp (z i).property
  constructor
  · exact h.1
  · omega

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def integerBoxMeshPointEquiv (lo hi : I → ℤ) :
    (∀ i, Finset.Ico (lo i) (hi i)) ≃ translatedIntegerBox lo (fun i => (hi i - lo i).toNat) where
  toFun := integerBoxMeshPoint lo hi
  invFun x i := ⟨x.val i, by
    have h := (mem_translatedIntegerBox _ _ _).mp x.property i
    exact Finset.mem_Ico.mpr ⟨h.1, by omega⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedScalarNestedPowerDetection
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

noncomputable def preparedEmptyLayerLocalLengthLog
    (m : ℕ) {K G : Type} [Fintype K] [Fintype G]
    (degree Cdetect : K → ℕ) (nX count : ℕ)
    (Bstruct pnum Qstride Qσ : ℝ) (u model : K → ℝ) (k : K) : ℝ :=
  let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
  let D := allocatedComparisonDimension m pnum
  let pDetect := fun k => allocatedModelTestLog (u k) (model k)
  let aDetect := fun k => 2 * u k + 4 * model k + 7
  let gain := fun k => slicedDetectionGainLog (degree k) (Cdetect k) count
    (pDetect k) (pDetect k) (aDetect k)
  let Pk := fun k => scalarKernelLogarithmicBudget (Fin (degree k + 1)) G
    (gain k + pDetect k + 4)
  let physical := fun k => preparedFiniteScheduleLocalPhysical m nX count Qstride (Pk k)
  let target := fun k => gain k + 40 + coefficientErrorSpatialLog (physical k)
  let E := fun k => target k + D * ((m * 2 ^ (m + 1) : ℕ) * Pk k) + 5
  let rho := fun k => 2 * affineProfileInputEnvelope D
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2) + 2
  let tail := fun k => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2)
  let scale := preparedUniformDegreeScaleLog (D + pRadius) tail Qσ
  let tmod := fun k => ((m + 1 : ℕ) : ℝ) * Pk k + nX * Qstride
  allocatedAffineLengthLog m D scale (rho k) (Pk k) (target k) (pDetect k + 2) (tmod k)

end Erdos3.VectorPolynomial

end

end OAI
end


