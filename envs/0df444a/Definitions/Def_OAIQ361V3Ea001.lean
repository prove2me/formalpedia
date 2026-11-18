-- Prove2me | Definitions.Def_OAIQ361V3Ea001
-- name    : OAIQ361V3Ea001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T16:24:04.875342+00:00
-- url     : https://prove2.me/theorems/a4894ca5-6f69-4d47-99e2-3ba70b7aab7e
-- title:
--   Definitions bundle OAIQ361V3Ea001 of the split of OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 406 declarations of OpenAI's Lean: 140 definitions, 22 instances and 244 theorems. The definitions and types are `OAI.EditApproximation.FiniteQuery.cost`, `OAI.EditApproximation.FiniteQuery.eraseSources`, `OAI.EditApproximation.FiniteQuery.keys`, `OAI.EditApproximation.FiniteQuery.substitute`, `OAI.EditApproximation.FiniteQuery.value`, `OAI.EditApproximation.LabeledEntry`, `OAI.EditApproximation.PhysicalLocalProgramKey`, `OAI.EditApproximation.PhysicalScalarDraw`, `OAI.EditApproximation.SourceRanked.projectedBody`, `OAI.EditApproximation.SourceRanked.value`, `OAI.EditApproximation.accuracyCutoff`, `OAI.EditApproximation.accuracyCutoffExponent`, `OAI.EditApproximation.adaptiveSeedLaw`, `OAI.EditApproximation.adaptiveSeedSequence`, `OAI.EditApproximation.adaptiveSeedStep`, `OAI.EditApproximation.balancedPieces`, `OAI.EditApproximation.bandActionCost`, `OAI.EditApproximation.bandActionEnvironment`, `OAI.EditApproximation.bernsteinEnvelope`, `OAI.EditApproximation.cacheEnvironment`, `OAI.EditApproximation.cellGroupEnvironment`, `OAI.EditApproximation.chargedEarlierWeight`, `OAI.EditApproximation.chargedSameWeight`, `OAI.EditApproximation.clipped`, `OAI.EditApproximation.coarseCanonicalDraws`, `OAI.EditApproximation.coarseChildListStart`, `OAI.EditApproximation.coarseDataListStart`, `OAI.EditApproximation.coarseEntryTailCount`, `OAI.EditApproximation.coarseExpectedArrayWork`, `OAI.EditApproximation.coarseFirstRequestWork`, `OAI.EditApproximation.coarseInternalNodes`, `OAI.EditApproximation.coarseInverseAllowanceFactor`, `OAI.EditApproximation.coarseLeftSweep`, `OAI.EditApproximation.coarsePenaltyTransform`, `OAI.EditApproximation.coarseTreeValue`, `OAI.EditApproximation.coarseWorkMultiplier`, `OAI.EditApproximation.comparisonActionCurvature`, `OAI.EditApproximation.comparisonActionMass`, `OAI.EditApproximation.comparisonPrefixShift`, `OAI.EditApproximation.comparisonPrefixSplice` and 100 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `EditApproximation_Binary_BinaryMemo`, `EditApproximation_Binary_BinarySampledGroupPolynomial`, `EditApproximation_Binary_BinarySampledOnlinePolynomial`, `EditApproximation_Binary_BinaryTriangularChoice`, `EditApproximation_Coarse_CoarseFirstRequestCost`, `EditApproximation_Coarse_CoarseGlobalSeed`, `EditApproximation_Coarse_CoarseInitial`, `EditApproximation_Coarse_CoarseProbability`, `EditApproximation_Coarse_CoarseSeed`, `EditApproximation_Coarse_CoarseTransforms`, `EditApproximation_Coarse_CoarseWork`, `EditApproximation_Coarse_CoarseWorkAsymptotics`, `EditApproximation_Geometry_Accuracy`, `EditApproximation_Geometry_AccuracyCutoff`, `EditApproximation_Geometry_ActualActionValues`, `EditApproximation_Geometry_ActualRoundedGroupInputs`, `EditApproximation_Geometry_AlignedStates`, `EditApproximation_Geometry_AlignmentSplitting`, `EditApproximation_Geometry_BalancedIntervals`, `EditApproximation_Geometry_BandActionPolynomial`, `EditApproximation_Geometry_BandDimension`, `EditApproximation_Geometry_BandEarlierDependence`, `EditApproximation_Geometry_BandGroupSampling`, `EditApproximation_Geometry_BandOptimizerWork`, `EditApproximation_Geometry_BandRegret`, `EditApproximation_Geometry_Bands`, `EditApproximation_Geometry_Bellman`, `EditApproximation_Geometry_CellGroupSelection`, `EditApproximation_Geometry_ChargedCoarseOracle`, `EditApproximation_Geometry_ChargedIndexCost`, `EditApproximation_Geometry_CommonRangeSource`, `EditApproximation_Geometry_ComparisonBandCoverage`, `EditApproximation_Geometry_ComparisonTree`, `EditApproximation_Geometry_ConeLocality`, `EditApproximation_Geometry_Cones`, `EditApproximation_Geometry_Connections`, `EditApproximation_Geometry_CurrentQueryInputs`, `EditApproximation_Geometry_DependencyExpansion`, `EditApproximation_Geometry_DomainCounts`, `EditApproximation_Geometry_EarlierInputBudget`, `EditApproximation_Geometry_EarlierValueDependence`, `EditApproximation_Geometry_FirstCrossing`, `EditApproximation_Geometry_GatheredLocalStep`, `EditApproximation_Geometry_Geometry`, `EditApproximation_Geometry_Grid`, `EditApproximation_Geometry_GroupCells`, `EditApproximation_Geometry_GroupInputDependence`, `EditApproximation_Geometry_GroupSampling`, `EditApproximation_Geometry_InitialConeGrid`, `EditApproximation_Geometry_InitialConeTable`, `EditApproximation_Geometry_InitialCones`, `EditApproximation_Geometry_Leaves`, `EditApproximation_Geometry_LocalGrid`, `EditApproximation_Geometry_LocalGroupSourceQuery`, `EditApproximation_Geometry_LocalInitialCones`, `EditApproximation_Geometry_LocalOnlineProgram`, `EditApproximation_Geometry_LocalRandomQueryKeys`, `EditApproximation_Geometry_LocalRefinementCones`, `EditApproximation_Geometry_NodeRegret`, `EditApproximation_Geometry_OccurrenceIndex`, `EditApproximation_Geometry_OnlineActionDraw`, `EditApproximation_Geometry_OnlineEarlierDependence`, `EditApproximation_Geometry_ParameterDependencyAsymptotics`, `EditApproximation_Geometry_Parameters`, `EditApproximation_Geometry_PartitionIntervals`, `EditApproximation_Geometry_PrefixBitEnvelope`, `EditApproximation_Geometry_PrefixComparison`, `EditApproximation_Geometry_PrefixCosts`, `EditApproximation_Geometry_PreparedBandPolynomial`, `EditApproximation_Geometry_PreparedCachedKernelWork`, `EditApproximation_Geometry_PreparedGroupPolynomial`, `EditApproximation_Geometry_PreparedLocalGroupPolynomial`, `EditApproximation_Geometry_RankedMemoKeys`, `EditApproximation_Geometry_RankedMemoProgram`, `EditApproximation_Geometry_RankedMemoSimulation`, `EditApproximation_Geometry_RankedMemoWork`, `EditApproximation_Geometry_RankedProgramRestriction`, `EditApproximation_Geometry_RefinementBandSupport`, `EditApproximation_Geometry_RefinementConeLocality`, `EditApproximation_Geometry_RefinementErrorTerms`, `EditApproximation_Geometry_Regret`, `EditApproximation_Geometry_RoundedGroupStates`, `EditApproximation_Geometry_SharedActions`, `EditApproximation_Geometry_SourceErasure`, `EditApproximation_Geometry_SourcePrefixes`, `EditApproximation_Geometry_SourceRankedProgram`, `EditApproximation_Geometry_SourceRankedWork`, `EditApproximation_Geometry_StateDomain`, `EditApproximation_Geometry_StateGeometry`, `EditApproximation_Geometry_WideActions`, `EditApproximation_Geometry_WideEarlierInputs`, `EditApproximation_Geometry_Work`, `EditApproximation_Numerics_NumericalWork`, `EditApproximation_Numerics_Numerics`, `EditApproximation_Numerics_RationalPruning`, `EditApproximation_Numerics_RationalRefinement`, `EditApproximation_Numerics_VectorOptimizerWork`, `EditApproximation_Probability_AdaptiveSeedLaw`, `EditApproximation_Probability_BernsteinEnvelope`, `EditApproximation_Probability_Exact`, `EditApproximation_Probability_ExactSampling`, `EditApproximation_Probability_FiniteAssignments`, `EditApproximation_Probability_FiniteProductWork`, `EditApproximation_Probability_FiniteQueryRestriction`, `EditApproximation_Probability_FiniteQueryWork`, `EditApproximation_Probability_FiniteSampling`, `EditApproximation_Probability_FiniteSeedFinal`, `EditApproximation_Probability_RejectionSelectedCost`, `EditApproximation_Queries_QueryDependencyExpansion`, `EditApproximation_Queries_QueryEarlierInputs`, `EditApproximation_Queries_QueryWeightedWork`, `EditApproximation_Refinement_ComputedCoarseWidthCost`, `EditApproximation_Refinement_ComputedCurrentQueryBudget`, `EditApproximation_Refinement_ComputedLocalKernelWork`, `EditApproximation_Refinement_ComputedPhysicalUniform`, `EditApproximation_Refinement_ComputedStageParameters`, `EditApproximation_Refinement_ComputedWarmupReadBudget`, `EditApproximation_Refinement_ComputedWidthEnvelope`, `EditApproximation_Refinement_PhysicalBoundsAllSeeds`, `EditApproximation_Refinement_PhysicalInitial`, `EditApproximation_Refinement_PhysicalInputEncoding`, `EditApproximation_Refinement_PhysicalLocalGroupKeys`, `EditApproximation_Refinement_PhysicalLocalOnlineKeys`, `EditApproximation_Refinement_PhysicalLocalProgramLaw`, `EditApproximation_Refinement_PhysicalNodeRegret`, `EditApproximation_Refinement_PhysicalProgramComparisonRegret`, `EditApproximation_Refinement_PhysicalProgramNodeRegret`, `EditApproximation_Refinement_PhysicalScalarFamily`, `EditApproximation_Refinement_PhysicalScalarFamilyLaw`, `EditApproximation_Refinement_PhysicalScalarReads`, `EditApproximation_Refinement_PhysicalScalarSource`, `EditApproximation_Refinement_PhysicalWarmup`, `EditApproximation_Refinement_PhysicalWarmupQuery`, `EditApproximation_Refinement_StageWarmup`, `EditDistance_Metric`.
--
--   **Imports.** It imports the published bundles `Def_EditApproxScheme_01`, `Def_EditApproxScheme_02`, `Def_EditApproxScheme_03`, `Def_EditApproxScheme_05`, `Def_EditApproxScheme_06`, `Def_EditApproxScheme_08`, `Def_EditApproxScheme_09`, `Def_EditApproxScheme_10`, `Def_EditApproxScheme_11`, `Def_EditApproxScheme_12`, `Def_EditApproxScheme_13`, `Def_EditApproxScheme_14`, `Def_EditApproxScheme_15` and `Def_EditApproxScheme_16`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ361V3Ea002` and `OAIQ361V3Ea003`; the statements `OAI.EditApproximation.computedExecutionTotalWork_expected_near_linear`, `OAI.EditApproximation.computedFamilyResult_requests_le`, `OAI.EditApproximation.computed_localRandomDataQuery_table_cost` and `OAI.EditApproximation.weighted_dependency_div_height_tendsto`; the proofs of `OAI.EditApproximation.BinaryFraction.cachedInitialProgramWithWork_cost`, `OAI.EditApproximation.BinaryFraction.coarseBinaryChildren_bounds`, `OAI.EditApproximation.BinaryFraction.computedCoarseInitialWithWork_bound`, `OAI.EditApproximation.BinaryFraction.computedCoarseRoot_for_candidate`, `OAI.EditApproximation.BinaryFraction.physicalContinuationWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsSourceWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.preparedLocalCellGroupsWithWork_cost`, `OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_complete_cost`, `OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_uniform_cost`, `OAI.EditApproximation.BinaryFraction.queryGroupRoundedStatesWithWork_bounds`, `OAI.EditApproximation.BinaryFraction.sampledGroupActionWithWork_cost` and `OAI.EditApproximation.weighted_dependency_div_height_tendsto`.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_EditApproxScheme_16

section
-- module Solutions.OAIQ361V3_EA.Compat
attribute [-instance] _root_.OAI.EditApproximation.physicalFamilyRange_neZero
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed non-unital ⋆-subalgebra of a C⋆-algebra is star ordered (d13f23b's `Subtype.starOrderedRing` is an
instance for every closed non-unital ⋆-subalgebra class; OpenAI's projection corners rely on it, q360). -/
instance nonUnitalStarSubalgebraStarOrderedRing {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (S : NonUnitalStarSubalgebra ℂ A) [IsClosed (S : Set A)] : StarOrderedRing S := by
  refine StarOrderedRing.of_nonneg_iff' (fun {a b} h c => ?_) (fun {s} => ?_)
  · show ((c : A) + (a : A)) ≤ (c : A) + (b : A)
    exact add_le_add le_rfl (show (a : A) ≤ (b : A) from h)
  · constructor
    · intro hs
      have hs' : (0 : A) ≤ (s : A) := hs
      have hmem : CFC.sqrt (s : A) ∈ S := by
        rw [CFC.sqrt_eq_real_sqrt _ hs']
        exact cfcₙ_mem (𝕜 := ℝ) (𝕜' := ℂ) (s := S) _ s.property
      refine ⟨⟨CFC.sqrt (s : A), hmem⟩, Subtype.ext ?_⟩
      show (s : A) = star (CFC.sqrt (s : A)) * CFC.sqrt (s : A)
      rw [CFC.sqrt_nonneg _ |>.isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self _ hs']
    · rintro ⟨t, rfl⟩
      show (0 : A) ≤ star (t : A) * (t : A)
      exact star_mul_self_nonneg _
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryMemo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A finite binary dictionary for gathered and globally memoized inputs.
Each recursive step reads one key bit and touches one node. The explicit
counters charge pointer/node operations; multiword key/value processing
is accounted for separately by their bit lengths. -/

namespace EditApproximation



/-- Fixed-width, least-significant-bit first encoding; no allocation
proportional to the numerical magnitude of a key is required. -/


@[simp] theorem binaryMemoKey_length (d n : ℕ) : (binaryMemoKey d n).length = d := by
  induction d generalizing n with
  | zero => rfl
  | succ d ih => simp only [binaryMemoKey, List.length_cons, ih]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Regret
attribute [-instance] _root_.OAI.EditApproximation.physicalFamilyRange_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Clipped Bellman regret for edit-distance refinement

The deterministic bound of Lemma `lem:generic-regret` in
Section 7 of *An Almost-Linear Approximation Scheme for Edit Distance*
(manuscript of September 24, 2026) applies to an arbitrary finite set of
children satisfying the Bellman inequality and exact-cost connection
inequality.
-/

namespace EditApproximation

open Finset

/-- Values are clipped at the exact cost only for the regret analysis. -/
def clipped (cost value : ℝ) : ℝ := max cost value

/-- Entropy plus the linear objective, with the manuscript's scaling. -/
noncomputable def entropyValue {ι : Type*} (coordinates : Finset ι)
    (η : ℝ) (objective p : ι → ℝ) : ℝ :=
  ∑ i ∈ coordinates, (Real.negMulLog (p i) + η * objective i * p i)

/-- The accumulated optimistic objective before a time index. -/
noncomputable def optimisticHistory {ι : Type*} (κ : ℝ)
    (gain decrement : ℕ → ι → ℝ) (t : ℕ) (i : ι) : ℝ :=
  ∑ j ∈ range t, (gain j i + (1 - 2 * κ) * decrement j i)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_Numerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Finite numerical optimizer for edit-distance refinement

These are the explicit fixed-step recurrence and rational mixture
calculations from Section 9 of *An Almost-Linear Approximation Scheme
for Edit Distance* (September 24, 2026). The recurrence is an internal
analytic obligation of the manuscript, not an assumed published theorem.
-/

namespace EditApproximation

open Finset

/-- The conditional-gradient step size in the finite entropy optimizer. -/
noncomputable def frankWolfeStep (j : ℕ) : ℝ := 2 / ((j : ℝ) + 2)

/-- Exact rational weight of the vertex selected at step `j`, after
`K` steps. -/
def optimizerMixtureWeight (K j : ℕ) : ℚ :=
  2 * ((j : ℚ) + 1) / ((K : ℚ) * ((K : ℚ) + 1))

/-- Exact rational conditional-gradient iterates. -/
def rationalOptimizerIterate {ι : Type*} (initial : ι → ℚ) (selected : ℕ → ι → ℚ) :
    ℕ → ι → ℚ
  | 0 => initial
  | j + 1 => fun i =>
    (1 - 2 / ((j : ℚ) + 2)) * rationalOptimizerIterate initial selected j i +
      (2 / ((j : ℚ) + 2)) * selected j i

noncomputable def smoothedEntropyValue {ι : Type*} (coordinates : Finset ι)
    (σ : ℝ) (linear p : ι → ℝ) : ℝ :=
  ∑ i ∈ coordinates, (Real.negMulLog (p i + σ) + linear i * p i)

noncomputable def smoothedEntropyGradient {ι : Type*}
    (σ : ℝ) (linear p : ι → ℝ) (i : ι) : ℝ :=
  -Real.log (p i + σ) - 1 + linear i

/-- The finite rational optimizer: every operation here is rational
arithmetic, finite enumeration, or the prescribed finite logarithm sum. -/


def finiteOptimizerSelection {ι : Type*} (coordinates : Finset ι)
    (vertices : List (ι → ℚ)) (linear : ι → ℚ) (G j : ℕ) : ι → ℚ :=
  rationalLinearizationMaximizer coordinates vertices
    (rationalSmoothedGradient G linear (finiteRationalOptimizer coordinates vertices linear G j))

def rationalVertexSet {ι : Type*} (vertices : List (ι → ℚ)) : Set (ι → ℝ) :=
  (fun p : ι → ℚ => fun i => (p i : ℝ)) '' {p | p ∈ vertices}

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_NumericalWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete numerical representation and arithmetic work

These are integer bit-length and exact rational-operation bounds for the
finite optimizer. They are not a RAM theorem: the costed evaluator below
counts rational arithmetic operations, while bit-operation costs also
require the charged evaluation model used by the surrounding algorithm.
-/

namespace EditApproximation

open Finset

/-- Costed repeated multiplication, counting one rational
multiplication at each successor. -/
def rationalPowerWithWork (r : ℚ) : ℕ → ℚ × ℕ
  | 0 => (1, 0)
  | n + 1 => let previous := rationalPowerWithWork r n
    (previous.1 * r, previous.2 + 1)

/-- The direct finite logarithm summation, with every power,
division and addition counted. -/
def rationalLogPartialWithWork (b : ℚ) : ℕ → ℚ × ℕ
  | 0 => (0, 0)
  | K + 1 =>
    let previous := rationalLogPartialWithWork b K
    let power := rationalPowerWithWork b (2 * K + 1)
    (previous.1 + power.1 / (2 * K + 1 : ℕ), previous.2 + power.2 + 2)

/-- Three operations form the logarithm parameter, and one final
multiplication doubles the partial sum. -/
def rationalLogApproximationWithWork (r : ℚ) (K : ℕ) : ℚ × ℕ :=
  let seriesResult := rationalLogPartialWithWork ((r - 1) / (r + 1)) K
  (2 * seriesResult.1, seriesResult.2 + 4)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandRegret
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Regret of the computed rational band mixtures

The optimistic objective is computed in rational arithmetic. The finite
optimizer supplies every predicted vector used here; no maximization
oracle or unproved entropy-regret hypothesis appears in the conclusion.
-/

namespace EditApproximation

open Finset



def computedOnlineVector {ι : Type*} (coordinates : Finset ι)
    (vertices : List (ι → ℚ)) (η κ : ℚ)
    (gain decrement : ℕ → ι → ℚ) (H t : ℕ) : ι → ℚ :=
  finiteRationalOptimizer coordinates vertices (rationalOnlineLinear η κ gain decrement t)
    (H + coordinates.card + 2) ((H + coordinates.card + 2) ^ 80)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_ExactSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Exact fair-bit sampling of the optimizer mixture

The finite-word rejection calculation follows Section 9.
The random trial is encoded from actual Boolean bits. First-success trace
probabilities determine the output law and expected number of trials.
-/

namespace EditApproximation

open Finset

/-- Number of fair bits per rejection trial. -/


theorem rejectionWord_range (N : ℕ) (hN : 0 < N) :
    N ≤ 2 ^ rejectionBitCount N ∧ 2 ^ rejectionBitCount N < 2 * N := by
  constructor
  · exact Nat.le_pow_clog (by norm_num) N
  · by_cases hNone : N = 1
    · subst N
      norm_num [rejectionBitCount]
    · have hN1 : 1 < N := by omega
      have hpred := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hN1
      have hB := Nat.clog_pos (by norm_num : 1 < 2) hN1
      have hpow : 2 ^ rejectionBitCount N = 2 ^ (Nat.clog 2 N).pred * 2 := by
        rw [rejectionBitCount, ← pow_succ]
        congr 1
        exact (Nat.succ_pred_eq_of_pos hB).symm
      rw [hpow]
      omega

/-- Rejection probability per trial. -/
noncomputable def rejectionFailureProbability (N R : ℕ) : ℝ := ((R - N : ℕ) : ℝ) / R

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_OnlineActionDraw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The finite rational optimizer samples actual band actions, retaining their labels through ties. -/

namespace EditApproximation

open Finset

theorem argmax_map_commutes {α β γ : Type*} [Preorder γ] [DecidableLT γ]
    (mapping : α → β) (score : β → γ) (values : List α) :
    (values.map mapping).argmax score = (values.argmax (fun a => score (mapping a))).map mapping := by
  induction values using List.reverseRecOn with
  | nil => rfl
  | append_singleton values a ih =>
    rw [List.map_append, List.map_singleton, List.argmax_concat, List.argmax_concat, ih]
    cases h : values.argmax (fun a => score (mapping a)) with
    | none => rfl
    | some selected =>
      simp only [Option.map_some]
      split_ifs <;> rfl



theorem finiteOptimizerAction_spec {β σ : Type*} [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : List (β → σ)) (hband : band ≠ []) (mass : β → ℚ)
    (linear : β × σ → ℚ) (G j : ℕ) :
    finiteOptimizerAction band hband mass linear G j ∈ band ∧
      actionVector mass (finiteOptimizerAction band hband mass linear G j) =
        finiteOptimizerSelection (bandCoordinates band.toFinset) (band.map (actionVector mass)) linear G j := by
  let coordinates := bandCoordinates band.toFinset
  let vertices := band.map (actionVector mass)
  let gradient := rationalSmoothedGradient G linear (finiteRationalOptimizer coordinates vertices linear G j)
  let score := fun action : β → σ => ∑ coordinate ∈ coordinates,
    gradient coordinate * actionVector mass action coordinate
  have hmap := argmax_map_commutes (actionVector mass)
    (fun vertex => ∑ coordinate ∈ coordinates, gradient coordinate * vertex coordinate) band
  cases harg : band.argmax score with
  | none => exact False.elim (hband (List.argmax_eq_none.mp harg))
  | some action =>
    have hmem : action ∈ band := List.argmax_mem (by rw [harg]; simp)
    have hvalue : finiteOptimizerAction band hband mass linear G j = action := by
      simp only [finiteOptimizerAction, score, coordinates, vertices, gradient] at harg ⊢
      rw [harg]
      rfl
    refine ⟨hvalue.symm ▸ hmem, ?_⟩
    rw [hvalue]
    unfold finiteOptimizerSelection rationalLinearizationMaximizer
    change actionVector mass action = (vertices.argmax
      (fun vertex => ∑ coordinate ∈ coordinates, gradient coordinate * vertex coordinate)).getD (fun _ => 0)
    change vertices.argmax (fun vertex => ∑ coordinate ∈ coordinates, gradient coordinate * vertex coordinate) =
      (band.argmax score).map (actionVector mass) at hmap
    rw [hmap, harg]
    rfl



theorem finiteOptimizerActionDraw_mem {β σ : Type*} [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : List (β → σ)) (hband : band ≠ []) (mass : β → ℚ)
    (linear : β × σ → ℚ) (G K : ℕ) (integer : Fin (optimizerTriangularMass K)) :
    finiteOptimizerActionDraw band hband mass linear G K integer ∈ band :=
  (finiteOptimizerAction_spec band hband mass linear G (triangularChoice K integer).val).1

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_VectorOptimizerWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Materialized rational optimizer iterates. Finite vectors store the
previous iterate and its gradient, and a scored scan stores the current
best score. Counters charge rational arithmetic, comparisons, array
accesses and array writes. Integer/rational bit costs are separate. -/

namespace EditApproximation

open Finset

def naturalPowerWithWork (a : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | k + 1 => let previous := naturalPowerWithWork a k
    (previous.1 * a, previous.2 + 1)

/-- Dot product over an explicit list of array indices. -/
def vectorDotListWithWork {d : ℕ} (left right : Vector ℚ d) : List (Fin d) → ℚ × ℕ
  | [] => (0, 0)
  | i :: indices =>
    let rest := vectorDotListWithWork left right indices
    (left.get i * right.get i + rest.1, rest.2 + 8)

def vectorDotWithWork {d : ℕ} (left right : Vector ℚ d) : ℚ × ℕ :=
  vectorDotListWithWork left right (List.finRange d)

def rationalGradientCellWithWork {d : ℕ} (G : ℕ) (linear point : Vector ℚ d) (i : Fin d) : ℚ × ℕ :=
  let smoothing := rationalPowerWithWork (G : ℚ) 50
  let truncation := naturalPowerWithWork G 60
  let logarithm := rationalLogApproximationWithWork (point.get i + 1 / smoothing.1) truncation.1
  (-logarithm.1 - 1 + linear.get i, smoothing.2 + truncation.2 + logarithm.2 + 7)

def vectorGradientWithWork {d : ℕ} (G : ℕ) (linear point : Vector ℚ d) : Vector ℚ d × ℕ :=
  vectorMapWithWork d (rationalGradientCellWithWork G linear point)

/-- A scored scan keeps the winning score instead of recomputing it.
It retains the first maximizer, including ties. -/
def scoredArgmaxWithWork {α : Type*} (score : α → ℚ × ℕ) : List α → Option (α × ℚ) × ℕ
  | [] => (none, 0)
  | a :: rest =>
    let tail := scoredArgmaxWithWork score rest
    let current := score a
    match tail.1 with
    | none => (some (a, current.1), tail.2 + current.2 + 1)
    | some best =>
      (if current.1 < best.2 then some best else some (a, current.1), tail.2 + current.2 + 2)

def vectorMaximizerWithWork {d : ℕ} (gradient : Vector ℚ d)
    (vertices : List (Vector ℚ d)) : Vector ℚ d × ℕ :=
  let selected := scoredArgmaxWithWork (vectorDotWithWork gradient) vertices
  ((selected.1.map Prod.fst).getD (Vector.replicate d 0), selected.2 + d + 1)

def materializedOptimizerWithWork {d : ℕ} (vertices : List (Vector ℚ d))
    (linear : Vector ℚ d) (G : ℕ) : ℕ → Vector ℚ d × ℕ
  | 0 => (vertices.headD (Vector.replicate d 0), d + 1)
  | j + 1 =>
    let previous := materializedOptimizerWithWork vertices linear G j
    let gradient := vectorGradientWithWork G linear previous.1
    let selected := vectorMaximizerWithWork gradient.1 vertices
    let step : ℚ := 2 / ((j : ℚ) + 2)
    let updated := vectorMapWithWork d fun i =>
      ((1 - step) * previous.1.get i + step * selected.1.get i, 5)
    (updated.1, previous.2 + gradient.2 + selected.2 + updated.2 + 3)

/-- The final scan retains the original action label, so equal vectors
and tied scores do not change which listed action is returned. -/
def materializedSelectionWithWork {α : Type*} {d : ℕ}
    (vertices : List (α × Vector ℚ d)) (linear : Vector ℚ d) (G j : ℕ) : Option α × ℕ :=
  let iterate := materializedOptimizerWithWork (vertices.map Prod.snd) linear G j
  let gradient := vectorGradientWithWork G linear iterate.1
  let selected := scoredArgmaxWithWork (fun vertex => vectorDotWithWork gradient.1 vertex.2) vertices
  (selected.1.map fun chosen => chosen.1.1, iterate.2 + gradient.2 + selected.2 + 1)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditDistance_Metric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Unrestricted edit scripts, metric inequalities, and common subsequences
-/

namespace EditDistortion

universe u v

variable {Alpha : Type u} {Beta : Type v} {s : Bool}

namespace Step

theorem symm {x y : List Alpha} (h : Step s x y) : Step s y x := by
  cases h with
  | insert p q a => exact .delete p q a
  | delete p q a => exact .insert p q a
  | substitute hs p q a b => exact .substitute hs p q b a

theorem append_left (p : List Alpha) {x y : List Alpha} (h : Step s x y) :
    Step s (p ++ x) (p ++ y) := by
  cases h with
  | insert q r a => simpa only [List.append_assoc] using Step.insert (substitutions := s) (p ++ q) r a
  | delete q r a => simpa only [List.append_assoc] using Step.delete (substitutions := s) (p ++ q) r a
  | substitute hs q r a b =>
    simpa only [List.append_assoc] using Step.substitute hs (p ++ q) r a b

theorem append_right (q : List Alpha) {x y : List Alpha} (h : Step s x y) :
    Step s (x ++ q) (y ++ q) := by
  cases h with
  | insert p r a =>
    simpa only [List.append_assoc, List.cons_append] using
      Step.insert (substitutions := s) p (r ++ q) a
  | delete p r a =>
    simpa only [List.append_assoc, List.cons_append] using
      Step.delete (substitutions := s) p (r ++ q) a
  | substitute hs p r a b =>
    simpa only [List.append_assoc, List.cons_append] using Step.substitute hs p (r ++ q) a b

theorem length_bounds {x y : List Alpha} (h : Step s x y) :
    x.length ≤ y.length + 1 ∧ y.length ≤ x.length + 1 := by
  cases h <;> simp only [List.length_append, List.length_cons] <;> omega

theorem allow_substitution {x y : List Alpha} (h : Step false x y) : Step true x y := by
  cases h with
  | insert p q a => exact .insert p q a
  | delete p q a => exact .delete p q a
  | substitute hs => cases hs

end Step

namespace Script

theorem trans {m n : ℕ} {x y z : List Alpha}
    (h : Script s m x y) (k : Script s n y z) : Script s (m + n) x z := by
  induction h with
  | nil => simpa using k
  | @cons l x w y e h ih =>
    simpa only [Nat.add_right_comm] using Script.cons e (ih k)

theorem single {x y : List Alpha} (h : Step s x y) : Script s 1 x y :=
  .cons h (.nil y)

theorem symm {n : ℕ} {x y : List Alpha} (h : Script s n x y) : Script s n y x := by
  induction h with
  | nil x => exact .nil x
  | cons e h ih => exact ih.trans (single e.symm)

theorem append_left (p : List Alpha) {n : ℕ} {x y : List Alpha} (h : Script s n x y) :
    Script s n (p ++ x) (p ++ y) := by
  induction h with
  | nil x => exact .nil _
  | cons e h ih => exact .cons (e.append_left p) ih

theorem append_right (q : List Alpha) {n : ℕ} {x y : List Alpha} (h : Script s n x y) :
    Script s n (x ++ q) (y ++ q) := by
  induction h with
  | nil x => exact .nil _
  | cons e h ih => exact .cons (e.append_right q) ih

theorem to_nil (x : List Alpha) : Script s x.length x [] := by
  induction x with
  | nil => exact .nil []
  | cons a x ih => exact .cons (.delete [] x a) ih

theorem exists_script (x y : List Alpha) : ∃ n, Script s n x y :=
  ⟨x.length + y.length, (to_nil x).trans (to_nil y).symm⟩

theorem length_bounds {n : ℕ} {x y : List Alpha} (h : Script s n x y) :
    x.length ≤ y.length + n ∧ y.length ≤ x.length + n := by
  induction h with
  | nil x => omega
  | cons e h ih => have := e.length_bounds; omega

theorem allow_substitution {n : ℕ} {x y : List Alpha} (h : Script false n x y) :
    Script true n x y := by
  induction h with
  | nil x => exact .nil x
  | cons e h ih => exact .cons e.allow_substitution ih

end Script



theorem cost_le {n : ℕ} {x y : List Alpha} (h : Script s n x y) : cost s x y ≤ n :=
  Nat.sInf_le h

theorem cost_spec (x y : List Alpha) : Script s (cost s x y) x y :=
  Nat.sInf_mem (Script.exists_script x y)

theorem cost_refl (x : List Alpha) : cost s x x = 0 :=
  Nat.eq_zero_of_le_zero (cost_le (.nil x))

theorem cost_symm (x y : List Alpha) : cost s x y = cost s y x := by
  apply Nat.le_antisymm
  · exact cost_le (cost_spec y x).symm
  · exact cost_le (cost_spec x y).symm

theorem cost_triangle (x y z : List Alpha) : cost s x z ≤ cost s x y + cost s y z :=
  cost_le ((cost_spec x y).trans (cost_spec y z))

theorem cost_length_bounds (x y : List Alpha) :
    x.length ≤ y.length + cost s x y ∧ y.length ≤ x.length + cost s x y :=
  (cost_spec x y).length_bounds

end EditDistortion

namespace EditDistortion

universe u v
variable {Alpha : Type u} {Beta : Type v} {s : Bool}

theorem Script.max_length (x y : List Alpha) : Script true (max x.length y.length) x y := by
  induction x generalizing y with
  | nil => simpa using (Script.to_nil (s := true) y).symm
  | cons a x ih =>
    cases y with
    | nil => simpa using Script.to_nil (s := true) (a :: x)
    | cons b y =>
      have hs := (ih y).append_left [b]
      have he := Step.substitute rfl [] x a b
      simpa only [List.length_cons, max_add_add_right, List.singleton_append, List.nil_append] using
        Script.cons he hs

theorem edit_le_max_length (x y : List Alpha) : edit x y ≤ max x.length y.length :=
  cost_le (Script.max_length x y)

theorem cost_append_le (x y u v : List Alpha) :
    cost s (x ++ u) (y ++ v) ≤ cost s x y + cost s u v :=
  cost_le (((cost_spec x y).append_right u).trans ((cost_spec u v).append_left y))

theorem Script.of_sublist {x y : List Alpha} (h : x.Sublist y) :
    Script false (y.length - x.length) y x := by
  induction h with
  | slnil => exact .nil []
  | @cons x y a h ih =>
    have hl := h.length_le
    simpa only [List.length_cons, Nat.succ_sub hl, Nat.succ_eq_add_one, List.nil_append] using
      Script.cons (.delete [] y a) ih
  | @cons_cons x y a h ih =>
    simpa only [List.length_cons, Nat.add_sub_add_right, List.singleton_append] using
      ih.append_left [a]

end EditDistortion

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Geometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Interval-state edit geometry

The edit distance here is the repository's unrestricted unit-cost
insertion/deletion/substitution distance, not an abstract metric supplied
as a hypothesis. These are the length and endpoint bounds in Section 2.
-/

namespace EditApproximation

open EditDistortion

universe u

theorem edit_sublist_le {α : Type u} {small large : List α} (h : small.Sublist large) :
    edit large small ≤ large.length - small.length :=
  cost_le (Script.of_sublist h).allow_substitution

theorem edit_drop_indices_le {α : Type u} (word : List α) (lo lo' : ℕ) :
    edit (word.drop lo) (word.drop lo') ≤ Nat.dist lo lo' := by
  rcases le_total lo lo' with h | h
  · have hs := edit_sublist_le (List.drop_sublist_drop_left word h)
    apply hs.trans
    simp only [List.length_drop, Nat.dist_eq_sub_of_le h]
    omega
  · rw [show edit (word.drop lo) (word.drop lo') =
        edit (word.drop lo') (word.drop lo) from cost_symm _ _]
    have hs := edit_sublist_le (List.drop_sublist_drop_left word h)
    apply hs.trans
    simp only [List.length_drop, Nat.dist_eq_sub_of_le_right h]
    omega

theorem edit_substring_right_le {α : Type u} (word : List α) (lo hi hi' : ℕ) :
    edit (substring word lo hi) (substring word lo hi') ≤ Nat.dist hi hi' := by
  rcases le_total hi hi' with h | h
  · have hs := edit_sublist_le ((List.take_sublist_take_left (l := word) h).drop lo)
    rw [show edit (substring word lo hi) (substring word lo hi') =
        edit (substring word lo hi') (substring word lo hi) from cost_symm _ _]
    apply hs.trans
    simp only [List.length_drop, List.length_take, Nat.dist_eq_sub_of_le h]
    omega
  · have hs := edit_sublist_le ((List.take_sublist_take_left (l := word) h).drop lo)
    apply hs.trans
    simp only [List.length_drop, List.length_take, Nat.dist_eq_sub_of_le_right h]
    omega

/-- Changing both substring endpoints costs at most their total movement,
including when the two intervals are disjoint. -/
theorem edit_substring_endpoints_le {α : Type u} (word : List α)
    (lo hi lo' hi' : ℕ) :
    edit (substring word lo hi) (substring word lo' hi') ≤
      Nat.dist lo lo' + Nat.dist hi hi' := by
  have htri := cost_triangle (s := true) (substring word lo hi)
    (substring word lo' hi) (substring word lo' hi')
  exact htri.trans (Nat.add_le_add (edit_drop_indices_le (word.take hi) lo lo')
    (edit_substring_right_le word lo' hi hi'))

theorem abs_length_gap_le_edit {α : Type u} (x y : List α) :
    |(y.length : ℝ) - x.length| ≤ (edit x y : ℝ) := by
  obtain ⟨hxy, hyx⟩ := cost_length_bounds (s := true) x y
  have hx : (x.length : ℝ) ≤ y.length + (edit x y : ℝ) := by exact_mod_cast hxy
  have hy : (y.length : ℝ) ≤ x.length + (edit x y : ℝ) := by exact_mod_cast hyx
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Connections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Connection costs with arbitrary gaps and overlaps

This proves the edit-cost part of the connection inequality of Section 2
for actual substrings and edit scripts. Prefixes telescope across the
child intervals; common-prefix cancellation then removes the outside
prefix. The children need not have ordered or shared target endpoints.
-/

namespace EditApproximation

open EditDistortion

universe u



/-- The outside and successive endpoint charges, including the final jump. -/


def targetConcatenation {α : Type u} (word : List α)
    (states : List (TargetInterval word.length)) : List α :=
  (states.map fun state => substring word state.lo state.hi).flatten

def signedLengthGap {α : Type u} (source target : List α) : ℝ :=
  (target.length : ℝ) - source.length

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_StateGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The finite domain of valid target states

The endpoint domain is enumerated by actual bounded natural loops. A
state's true cost and signed length gap use the stored target substring.
-/

namespace EditApproximation

open EditDistortion





theorem natural_distance_cast (a b : ℕ) : |(a : ℝ) - b| = (Nat.dist a b : ℝ) := by
  rcases le_total a b with h | h
  · have hR : (a : ℝ) ≤ b := by exact_mod_cast h
    rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_of_nonpos (sub_nonpos.mpr hR)]
    ring
  · have hR : (b : ℝ) ≤ a := by exact_mod_cast h
    rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr hR)]

noncomputable def stateEditCost {α : Type*} (source target : List α) (q : TargetInterval target.length) : ℕ :=
  edit source (substring target q.lo q.hi)

def stateLengthGap {α : Type*} (source target : List α) (q : TargetInterval target.length) : ℝ :=
  (q.hi : ℝ) - q.lo - source.length

theorem stateLengthGap_actual {α : Type*} (source target : List α)
    (q : TargetInterval target.length) :
    stateLengthGap source target q = signedLengthGap source (substring target q.lo q.hi) := by
  have hlength : (substring target q.lo q.hi).length = q.hi - q.lo := by
    simp only [substring, List.length_drop, List.length_take, Nat.min_eq_left q.valid]
  unfold stateLengthGap signedLengthGap
  rw [hlength, Nat.cast_sub q.ordered]

theorem stateEditCost_length_lower {α : Type*} (source target : List α)
    (q : TargetInterval target.length) :
    |stateLengthGap source target q| ≤ stateEditCost source target q := by
  rw [stateLengthGap_actual]
  exact abs_length_gap_le_edit source (substring target q.lo q.hi)

theorem stateEditCost_spatial {α : Type*} (source target : List α)
    (q r : TargetInterval target.length) :
    stateEditCost source target q ≤ stateEditCost source target r + targetEndpointDistance q r := by
  have hmove := edit_substring_endpoints_le target r.lo r.hi q.lo q.hi
  have htriangle := cost_triangle (s := true) source
    (substring target r.lo r.hi) (substring target q.lo q.hi)
  change edit source (substring target q.lo q.hi) ≤
    edit source (substring target r.lo r.hi) + edit (substring target r.lo r.hi) (substring target q.lo q.hi)
    at htriangle
  change edit source (substring target q.lo q.hi) ≤
    edit source (substring target r.lo r.hi) + (Nat.dist q.lo r.lo + Nat.dist q.hi r.hi)
  rw [Nat.dist_comm r.lo q.lo, Nat.dist_comm r.hi q.hi] at hmove
  omega

theorem stateLengthGap_spatial {α : Type*} (source target : List α)
    (q r : TargetInterval target.length) :
    |stateLengthGap source target q| ≤ |stateLengthGap source target r| + targetEndpointDistance q r := by
  have hlo : |(q.lo : ℝ) - r.lo| = Nat.dist q.lo r.lo := by
    exact natural_distance_cast q.lo r.lo
  have hhi : |(q.hi : ℝ) - r.hi| = Nat.dist q.hi r.hi := by
    exact natural_distance_cast q.hi r.hi
  have hdiff : stateLengthGap source target q - stateLengthGap source target r =
      ((q.hi : ℝ) - r.hi) - ((q.lo : ℝ) - r.lo) := by unfold stateLengthGap; ring
  have hmetric : |stateLengthGap source target q - stateLengthGap source target r| ≤
      (targetEndpointDistance q r : ℝ) := by
    rw [hdiff]
    have habs := abs_sub ((q.hi : ℝ) - r.hi) ((q.lo : ℝ) - r.lo)
    rw [hhi, hlo] at habs
    simpa only [targetEndpointDistance, Nat.cast_add, add_comm] using habs
  have h := (abs_sub_abs_le_abs_sub _ _).trans hmetric
  linarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Bellman
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite Bellman propagation and warmup

The action minimum is computed by a finite list with the initial cone as
fallback. Empty action families need no extended-real convention. The
warmup lemmas concern the actual repeated finite Bellman operator.
-/

namespace EditApproximation

open Finset

def finiteMinimum (fallback : ℝ) : List ℝ → ℝ
  | [] => fallback
  | value :: rest => min value (finiteMinimum fallback rest)

theorem finiteMinimum_map_mono {ι : Type*} (indices : List ι)
    (fallback fallback' : ℝ) (value value' : ι → ℝ)
    (hfallback : fallback ≤ fallback') (hvalue : ∀ i ∈ indices, value i ≤ value' i) :
    finiteMinimum fallback (indices.map value) ≤
      finiteMinimum fallback' (indices.map value') := by
  induction indices with
  | nil => exact hfallback
  | cons i rest ih =>
    simp only [List.map_cons, finiteMinimum]
    exact min_le_min (hvalue i (by simp)) (ih fun j hj => hvalue j (by simp [hj]))

theorem finiteMinimum_map_add {ι : Type*} (indices : List ι)
    (fallback charge : ℝ) (value : ι → ℝ) :
    finiteMinimum (fallback + charge) (indices.map fun i => value i + charge) =
      finiteMinimum fallback (indices.map value) + charge := by
  induction indices with
  | nil => rfl
  | cons i rest ih => simp only [List.map_cons, finiteMinimum, ih, min_add_add_right]

theorem finiteMinimum_map_spatial {ι : Type*} (indices : List ι)
    (fallback fallback' charge : ℝ) (value value' : ι → ℝ)
    (hfallback : fallback ≤ fallback' + charge)
    (hvalue : ∀ i ∈ indices, value i ≤ value' i + charge) :
    finiteMinimum fallback (indices.map value) ≤
      finiteMinimum fallback' (indices.map value') + charge := by
  rw [← finiteMinimum_map_add]
  exact finiteMinimum_map_mono indices _ _ _ _ hfallback hvalue

def warmup {State : Type*} (operator : (State → ℝ) → State → ℝ)
    (initial : State → ℝ) : ℕ → State → ℝ
  | 0 => initial
  | t + 1 => operator (warmup operator initial t)

noncomputable def warmupAverage {State : Type*}
    (operator : (State → ℝ) → State → ℝ) (initial : State → ℝ)
    (T : ℕ) (state : State) : ℝ :=
  (∑ t ∈ range T, warmup operator initial t state) / T

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Cones
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scalar steps of the refinement update

These are the min/max and first-crossing calculations in Sections 5 and 7
of *An Almost-Linear Approximation Scheme for Edit Distance* (2026).
They are internal lemmas, not the main algorithmic theorem.
-/

namespace EditApproximation

/-- The nonzero branch of the refinement update, for a nonempty online list.
An empty list returns the cone minimum directly. -/
noncomputable def refinementUpdate (δ cone online : ℝ) : ℝ :=
  min cone (max (cone / (1 + δ)) online)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_RationalRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Rational execution of the Bellman and refinement operations

Every finite minimum, cone cost, warmup iteration, and refinement update
is computed in rational arithmetic. The real analysis used elsewhere is
the exact cast of these operations. An absent online candidate returns
the cone minimum, avoiding an extended-real value in the implementation.
-/

namespace EditApproximation



theorem rationalMinimum_cast (fallback : ℚ) (values : List ℚ) :
    (rationalMinimum fallback values : ℝ) = finiteMinimum (fallback : ℝ) (values.map Rat.cast) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [rationalMinimum, finiteMinimum, List.map_cons, Rat.cast_min, ih]



def rationalWarmup {State : Type*} (operator : (State → ℚ) → State → ℚ)
    (initial : State → ℚ) : ℕ → State → ℚ
  | 0 => initial
  | t + 1 => operator (rationalWarmup operator initial t)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_InitialCones
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Rational scaled seeds and the actual cone lower invariant

Ceilings preserve the upper bound because `F*c` is an integer. Cone lower
bounds use the actual edit-distance and signed-length geometry, rather
than an assumed lower-bound-preserving cone oracle.
-/

namespace EditApproximation



theorem rationalStateGap_cast {α : Type*} (source target : List α)
    (q : TargetInterval target.length) :
    (rationalStateGap source target q : ℝ) = stateLengthGap source target q := by
  simp only [rationalStateGap, stateLengthGap, Rat.cast_sub, Rat.cast_natCast]



theorem scaledSeedValue_bounds (U c F : ℕ) (a gap : ℚ)
    (ha : 1 ≤ a) (hF : 1 ≤ F) (hU : c ≤ U)
    (hupper : (U : ℚ) ≤ a * F * c) (hgap : |gap| ≤ c) :
    max ((c : ℚ) / a) |gap| ≤ scaledSeedValue U a gap ∧ scaledSeedValue U a gap ≤ F * c := by
  have ha0 : 0 < a := by linarith
  have hFQ : (1 : ℚ) ≤ F := by exact_mod_cast hF
  have hc0 : (0 : ℚ) ≤ c := Nat.cast_nonneg c
  have hratio : (U : ℚ) / a ≤ F * c := by
    apply (div_le_iff₀ ha0).2
    nlinarith
  have hceil : ⌈(U : ℚ) / a⌉₊ ≤ F * c := Nat.ceil_le.mpr (by exact_mod_cast hratio)
  constructor
  · apply max_le_max _ le_rfl
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hU) ha0.le).trans (Nat.le_ceil _)
  · apply max_le (by exact_mod_cast hceil) _
    exact hgap.trans (by nlinarith)

theorem scaledSeedValue_zero (a : ℚ) : scaledSeedValue 0 a 0 = 0 := by
  simp only [scaledSeedValue, Nat.cast_zero, zero_div, Nat.ceil_zero, abs_zero, max_self]



theorem initialConeValue_actual_lower {α : Type*} (source target : List α)
    (U : TargetInterval target.length → ℕ) (a L0 : ℚ)
    (query center : TargetInterval target.length) (ha : 1 ≤ a) (hL : 1 ≤ L0)
    (hseed : stateEditCost source target center ≤ U center) :
    max ((stateEditCost source target query : ℚ) / a) |rationalStateGap source target query| ≤
      initialConeValue source target U a L0 query center := by
  have ha0 : 0 < a := by linarith
  let distance : ℚ := targetEndpointDistance query center
  let base := scaledSeedValue (U center) a (rationalStateGap source target center)
  have hd0 : 0 ≤ distance := Nat.cast_nonneg _
  have hbaseCost : (stateEditCost source target center : ℚ) / a ≤ base :=
    (div_le_div_of_nonneg_right (by exact_mod_cast hseed) ha0.le).trans
      ((Nat.le_ceil _).trans (le_max_left _ _))
  have hbaseGap : |rationalStateGap source target center| ≤ base := le_max_right _ _
  have hdistDiv : distance / a ≤ distance := by
    apply (div_le_iff₀ ha0).2
    nlinarith
  have hdistSlope : distance ≤ L0 * distance := by nlinarith
  have hcost : (stateEditCost source target query : ℚ) ≤ stateEditCost source target center + distance := by
    dsimp only [distance]
    exact_mod_cast stateEditCost_spatial source target query center
  have hgap : |rationalStateGap source target query| ≤ |rationalStateGap source target center| + distance := by
    have h := stateLengthGap_spatial source target query center
    rw [← rationalStateGap_cast, ← rationalStateGap_cast] at h
    exact_mod_cast h
  change max ((stateEditCost source target query : ℚ) / a) |rationalStateGap source target query| ≤
    base + L0 * distance
  apply max_le
  · have hdivide := div_le_div_of_nonneg_right hcost ha0.le
    rw [add_div] at hdivide
    linarith
  · linarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_AlignmentSplitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Splitting an optimal edit script at a source cut

An arbitrary unrestricted edit script transports a cut through its
intermediate strings. Each edit belongs to one side of that cut. Applied
to a shortest script, this gives an exact optimal target split, including
empty source or target pieces.
-/

namespace EditApproximation

open EditDistortion

universe u

theorem step_split {α : Type u} {x y : List α} (step : Step true x y)
    (left right : List α) (hx : x = left ++ right) :
    ∃ left' right', y = left' ++ right' ∧
      ((Step true left left' ∧ right = right') ∨
        (left = left' ∧ Step true right right')) := by
  cases step with
  | insert p q a =>
    rcases List.append_eq_append_iff.mp hx.symm with ⟨mid, hp, hr⟩ | ⟨mid, hl, hq⟩
    · refine ⟨left, mid ++ a :: q, ?_, Or.inr ⟨rfl, ?_⟩⟩
      · simp only [hp, List.append_assoc]
      · rw [hr]
        exact Step.insert mid q a
    · refine ⟨p ++ a :: mid, right, ?_, Or.inl ⟨?_, rfl⟩⟩
      · simp only [hq, List.append_assoc, List.cons_append]
      · rw [hl]
        exact Step.insert p mid a
  | delete p q a =>
    rcases List.append_eq_append_iff.mp hx.symm with ⟨mid, hp, hr⟩ | ⟨mid, hl, hq⟩
    · refine ⟨left, mid ++ q, ?_, Or.inr ⟨rfl, ?_⟩⟩
      · simp only [hp, List.append_assoc]
      · rw [hr]
        exact Step.delete mid q a
    · cases mid with
      | nil =>
        simp only [List.append_nil] at hl
        simp only [List.nil_append] at hq
        refine ⟨left, q, ?_, Or.inr ⟨rfl, ?_⟩⟩
        · rw [hl]
        · rw [← hq]
          exact Step.delete [] q a
      | cons b mid =>
        simp only [List.cons_append, List.cons.injEq] at hq
        rcases hq with ⟨rfl, hq⟩
        refine ⟨p ++ mid, right, ?_, Or.inl ⟨?_, rfl⟩⟩
        · simp only [hq, List.append_assoc]
        · rw [hl]
          exact Step.delete p mid a
  | substitute _ p q a b =>
    rcases List.append_eq_append_iff.mp hx.symm with ⟨mid, hp, hr⟩ | ⟨mid, hl, hq⟩
    · refine ⟨left, mid ++ b :: q, ?_, Or.inr ⟨rfl, ?_⟩⟩
      · simp only [hp, List.append_assoc]
      · rw [hr]
        exact Step.substitute rfl mid q a b
    · cases mid with
      | nil =>
        simp only [List.append_nil] at hl
        simp only [List.nil_append] at hq
        refine ⟨left, b :: q, ?_, Or.inr ⟨rfl, ?_⟩⟩
        · rw [hl]
        · rw [← hq]
          exact Step.substitute rfl [] q a b
      | cons c mid =>
        simp only [List.cons_append, List.cons.injEq] at hq
        rcases hq with ⟨rfl, hq⟩
        refine ⟨p ++ b :: mid, right, ?_, Or.inl ⟨?_, rfl⟩⟩
        · simp only [hq, List.append_assoc, List.cons_append]
        · rw [hl]
          exact Step.substitute rfl p mid a b

theorem script_split {α : Type u} {x y : List α} {n : ℕ}
    (script : Script true n x y) (left right : List α) (hx : x = left ++ right) :
    ∃ left' right' nleft nright,
      y = left' ++ right' ∧ nleft + nright = n ∧
        Script true nleft left left' ∧ Script true nright right right' := by
  induction script generalizing left right with
  | nil x => exact ⟨left, right, 0, 0, hx, rfl, .nil _, .nil _⟩
  | @cons n x y z step rest ih =>
    obtain ⟨midleft, midright, hy, hs⟩ := step_split step left right hx
    obtain ⟨lastleft, lastright, nl, nr, hz, hn, hleft, hright⟩ :=
      ih midleft midright hy
    rcases hs with ⟨hstep, rfl⟩ | ⟨rfl, hstep⟩
    · exact ⟨lastleft, lastright, nl + 1, nr, hz, by omega,
        .cons hstep hleft, hright⟩
    · exact ⟨lastleft, lastright, nl, nr + 1, hz, by omega,
        hleft, .cons hstep hright⟩

/-- A shortest unrestricted edit script admits an exactly optimal split
at every source cut. -/
theorem edit_append_split {α : Type u} (left right target : List α) :
    ∃ targetLeft targetRight, target = targetLeft ++ targetRight ∧
      edit (left ++ right) target = edit left targetLeft + edit right targetRight := by
  obtain ⟨tl, tr, nl, nr, ht, hn, hl, hr⟩ :=
    script_split (cost_spec (s := true) (left ++ right) target) left right rfl
  refine ⟨tl, tr, ht, Nat.le_antisymm ?_ ?_⟩
  · rw [ht]
    exact cost_append_le (s := true) left tl right tr
  · have hleft := cost_le hl
    have hright := cost_le hr
    change edit left tl ≤ nl at hleft
    change edit right tr ≤ nr at hright
    change nl + nr = edit (left ++ right) target at hn
    omega

/-- Repeated source cuts have a common ordered target partition whose
piecewise edit costs sum exactly to the parent optimum. Source pieces
may be empty. A nonempty list of pieces is needed to assign insertions. -/
theorem edit_partition_split {α : Type u} (parts : List (List α))
    (hne : parts ≠ []) (target : List α) :
    ∃ targetParts : List (List α), targetParts.length = parts.length ∧
      targetParts.flatten = target ∧
      (List.zipWith edit parts targetParts).sum = edit parts.flatten target := by
  induction parts generalizing target with
  | nil => exact False.elim (hne rfl)
  | cons first rest ih =>
    cases rest with
    | nil =>
      refine ⟨[target], rfl, ?_, ?_⟩
      · simp
      · simp
    | cons second rest =>
      obtain ⟨tl, tr, ht, hc⟩ := edit_append_split first (second :: rest).flatten target
      obtain ⟨targets, hlen, hflatten, hcost⟩ := ih (by simp) tr
      refine ⟨tl :: targets, by simp only [List.length_cons, hlen], ?_, ?_⟩
      · simp only [List.flatten_cons, hflatten]
        exact ht.symm
      · simp only [List.flatten_cons, List.zipWith_cons_cons, List.sum_cons, hcost]
        exact hc.symm

/-- Prefixes of an ordered source/target partition use at most the
partition's total edit cost. This bounds every alignment anchor shift. -/
theorem edit_partition_prefix_le {α : Type u}
    (parts targets : List (List α)) (hlen : parts.length = targets.length) (k : ℕ) :
    edit (parts.take k).flatten (targets.take k).flatten ≤
      (List.zipWith edit parts targets).sum := by
  induction parts generalizing targets k with
  | nil =>
    have ht : targets = [] := List.length_eq_zero_iff.mp hlen.symm
    subst targets
    simp only [List.take_nil, List.flatten_nil, List.zipWith_nil_left, List.sum_nil]
    exact (cost_refl ([] : List α)).le
  | cons first rest ih =>
    cases targets with
    | nil => simp at hlen
    | cons targetFirst targetRest =>
      have hrest : rest.length = targetRest.length := by simpa using hlen
      cases k with
      | zero =>
        simp only [List.take_zero, List.flatten_nil]
        exact (cost_refl ([] : List α)).le.trans (Nat.zero_le _)
      | succ k =>
        simp only [List.take_succ_cons, List.flatten_cons, List.zipWith_cons_cons, List.sum_cons]
        exact (cost_append_le (s := true) first targetFirst
          (rest.take k).flatten (targetRest.take k).flatten).trans
            (Nat.add_le_add_left (ih targetRest hrest k) _)

theorem optimal_partition_anchor_shift_bound {α : Type u}
    (parts targets : List (List α)) (target : List α)
    (hlen : parts.length = targets.length)
    (hcost : (List.zipWith edit parts targets).sum = edit parts.flatten target) (k : ℕ) :
    |((targets.take k).flatten.length : ℝ) - (parts.take k).flatten.length| ≤
      (edit parts.flatten target : ℝ) := by
  apply (abs_length_gap_le_edit (parts.take k).flatten (targets.take k).flatten).trans
  exact_mod_cast (edit_partition_prefix_le parts targets hlen k).trans_eq hcost

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Leaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Exact interval-tree leaves

An occurrence query gives the exact unit-cost edit distance at a source
leaf of width one (Section 2 of the manuscript).
-/

namespace EditApproximation

open EditDistortion

universe u

/-- The part of the singleton cost determined by length and occurrence. -/


theorem occurrenceDeficit_le_length {α : Type u} [DecidableEq α]
    (a : α) (word : List α) : occurrenceDeficit a word ≤ word.length := Nat.sub_le _ _

theorem length_le_occurrenceDeficit_add_one {α : Type u} [DecidableEq α]
    (a : α) (word : List α) : word.length ≤ occurrenceDeficit a word + 1 := by
  unfold occurrenceDeficit
  split_ifs <;> omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseSeed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The actual bounded-shift coarse tree

Section 3's deterministic shift representation uses a complete finite
branching tree with empty/singleton source leaves. Bounded integer shifts
are encoded by `Fin (2k+1)`; code `k` is shift zero. Virtual target positions
are represented by fresh `none` symbols in a finite surrounding frame.
-/

namespace EditApproximation

open Finset EditDistortion

universe u




/-- The zero root shift is the middle integer code. -/


def coarseTreeValue {B D : ℕ} {α : Type u} [DecidableEq α]
    (tree : CoarseSourceTree B α D) (target : List α) (k : ℕ) : ℕ :=
  coarseShiftCost k (coarseTargetFrame k target) tree 0 (coarseRootShift k)

theorem substring_split {α : Type u} (word : List α) (lo mid hi : ℕ)
    (hlo : lo ≤ mid) (hhi : mid ≤ hi) :
    substring word lo hi = substring word lo mid ++ substring word mid hi := by
  have hindex : lo + (mid - lo) = mid := by omega
  calc
    _ = ((substring word lo hi).take (mid - lo)) ++
        ((substring word lo hi).drop (mid - lo)) := (List.take_append_drop _ _).symm
    _ = _ := by
      simp only [substring, List.take_drop, List.take_take, List.drop_drop, hindex,
        Nat.min_eq_left hhi]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BalancedIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The actual balanced interval cuts

The fixed interval tree uses cuts `l + floor(i*width/M)`. Their substring
pieces concatenate exactly to the parent, including repeated cuts and
empty pieces. These facts instantiate optimal alignment splitting on the
manuscript's actual source intervals.
-/

namespace EditApproximation



theorem balancedCut_last (lo width M : ℕ) (hM : 0 < M) :
    balancedCut lo width M M = lo + width := by
  simp only [balancedCut, Nat.mul_div_cancel_left _ hM]

theorem balancedCut_monotone (lo width M : ℕ) : Monotone (balancedCut lo width M) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.div_le_div_right (Nat.mul_le_mul_right width hij)) lo

theorem balancedCut_bounds (lo width M i : ℕ) (hM : 0 < M) (hi : i ≤ M) :
    lo ≤ balancedCut lo width M i ∧ balancedCut lo width M i ≤ lo + width := by
  constructor
  · exact Nat.le_add_right _ _
  · rw [← balancedCut_last lo width M hM]
    exact balancedCut_monotone lo width M hi

def balancedPieces {α : Type*} (word : List α) (lo width M : ℕ) : List (List α) :=
  (List.range M).map fun i => substring word (balancedCut lo width M i) (balancedCut lo width M (i + 1))

theorem balancedPieces_prefix {α : Type*} (word : List α) (lo width M j : ℕ) :
    ((List.range j).map fun i =>
      substring word (balancedCut lo width M i) (balancedCut lo width M (i + 1))).flatten =
        substring word lo (balancedCut lo width M j) := by
  induction j with
  | zero => simp [balancedCut, substring]
  | succ j ih =>
    rw [List.range_succ, List.map_append, List.flatten_append]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [ih]
    exact (substring_split word lo (balancedCut lo width M j) (balancedCut lo width M (j + 1))
      (Nat.le_add_right _ _) (balancedCut_monotone lo width M (Nat.le_succ j))).symm

theorem balancedPieces_flatten {α : Type*} (word : List α) (lo width M : ℕ) (hM : 0 < M) :
    (balancedPieces word lo width M).flatten = substring word lo (lo + width) := by
  rw [balancedPieces, balancedPieces_prefix, balancedCut_last lo width M hM]

theorem balancedPieces_length {α : Type*} (word : List α) (lo width M : ℕ) :
    (balancedPieces word lo width M).length = M := by
  simp only [balancedPieces, List.length_map, List.length_range]





theorem sourceChild_partition {α : Type*} (word : List α) {M : ℕ} (hM : 0 < M)
    (parent : TargetInterval word.length) :
    (List.ofFn fun child : Fin M =>
      substring word (sourceChild parent child).lo (sourceChild parent child).hi).flatten =
        substring word parent.lo parent.hi := by
  have hlist : (List.ofFn fun child : Fin M =>
      substring word (sourceChild parent child).lo (sourceChild parent child).hi) =
      balancedPieces word parent.lo (parent.hi - parent.lo) M := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, balancedPieces_length]
    · intro i hi hj
      simp only [List.getElem_ofFn, balancedPieces, List.getElem_map, List.getElem_range, sourceChild]
  rw [hlist, balancedPieces_flatten word parent.lo (parent.hi - parent.lo) M hM,
    Nat.add_sub_of_le parent.ordered]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ActualActionValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Connection values at labeled physical children

Child table values retain their child labels even when two source
substrings coincide. The edit and shift lower bounds are proved for
the actual finite sum of these labeled values.
-/

namespace EditApproximation

open Finset EditDistortion



noncomputable def endpointActionValue {n M : ℕ} (q : TargetInterval n)
    (states : Fin M → TargetInterval n) (value : Fin M → TargetInterval n → ℝ) : ℝ :=
  endpointActionConnection q states + ∑ i, value i (states i)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Integer endpoint grids

Rounding is an executable integer division. It preserves valid interval
states and shared endpoints, and the edit-distance perturbation is bounded
by the actual two remainders. No real-valued grid is substituted for it.
-/

namespace EditApproximation



theorem gridRound_distance (spacing position : ℕ) :
    Nat.dist position (gridRound spacing position) = position % spacing := by
  have h := Nat.mod_add_div position spacing
  unfold Nat.dist gridRound
  omega

theorem gridRound_error_lt (spacing position : ℕ) (hspacing : 0 < spacing) :
    Nat.dist position (gridRound spacing position) < spacing := by
  rw [gridRound_distance]
  exact Nat.mod_lt _ hspacing

theorem gridRound_of_dvd {spacing position : ℕ} (hdiv : spacing ∣ position) :
    gridRound spacing position = position := by
  have hzero := Nat.mod_eq_zero_of_dvd hdiv
  have h := Nat.mod_add_div position spacing
  simpa only [hzero, zero_add, gridRound] using h

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SharedActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact connection cancellation for shared-endpoint finite actions. -/

namespace EditApproximation

theorem connectionBudget_ofFn_zero {n : ℕ} (M : ℕ) (states : Fin M → TargetInterval n)
    (start finish : ℕ)
    (hstart : ∀ i : Fin M, i.val = 0 → start = (states i).lo)
    (hnext : ∀ i j : Fin M, j.val = i.val + 1 → (states i).hi = (states j).lo)
    (hend : ∀ i : Fin M, i.val + 1 = M → (states i).hi = finish)
    (hempty : M = 0 → start = finish) :
    connectionBudget start (List.ofFn states) finish = 0 := by
  induction M generalizing start with
  | zero => simp only [List.ofFn_zero, connectionBudget, hempty rfl, Nat.dist_self]
  | succ M ih =>
    rw [List.ofFn_succ, connectionBudget, hstart 0 rfl, Nat.dist_self, zero_add]
    apply ih (fun i => states i.succ) (states 0).hi
    · intro i hi
      exact hnext 0 i.succ (by simp only [Fin.val_zero, Fin.val_succ]; omega)
    · intro i j hij
      exact hnext i.succ j.succ (by simp only [Fin.val_succ]; omega)
    · intro i hi
      exact hend i.succ (by simp only [Fin.val_succ]; omega)
    · intro hM
      exact hend 0 (by simp only [Fin.val_zero]; omega)

theorem endpointActionConnection_zero {n M : ℕ} (hM : 0 < M) (q : TargetInterval n)
    (states : Fin M → TargetInterval n)
    (hstart : (states ⟨0, hM⟩).lo = q.lo)
    (hend : (states ⟨M - 1, by omega⟩).hi = q.hi)
    (hnext : ∀ i j : Fin M, j.val = i.val + 1 → (states i).hi = (states j).lo) :
    endpointActionConnection q states = 0 := by
  apply connectionBudget_ofFn_zero
  · intro i hi
    have heq : i = ⟨0, hM⟩ := Fin.ext hi
    rw [heq]
    exact hstart.symm
  · exact hnext
  · intro i hi
    have heq : i = ⟨M - 1, by omega⟩ := Fin.ext (by change i.val = M - 1; omega)
    rw [heq]
    exact hend
  · omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PrefixCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite prefix costs used by the predicted bands

A prefix is a restriction of an enumerated wide action. The last jump is
evaluated at the proposed real shift. Taking the minimum over the actual
finite list, with its first member duplicated as the fallback, gives the
exact prefix minimum and its 1-Lipschitz property.
-/

namespace EditApproximation

open Finset

noncomputable def realConnectionBudget {n : ℕ} (start : ℝ) :
    List (TargetInterval n) → ℝ → ℝ
  | [], finish => |start - finish|
  | state :: rest, finish => |start - state.lo| + realConnectionBudget state.hi rest finish

noncomputable def widePrefixCost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (states : Fin M → TargetInterval ny)
    (child : Fin M → TargetInterval ny → ℝ) (j : ℕ) (p : ℝ) : ℝ :=
  realConnectionBudget r.lo ((List.ofFn states).take j)
    ((balancedCut parent.lo (parent.hi - parent.lo) M j : ℝ) + p) +
      ∑ i, if i.val < j then child i (states i) else 0

noncomputable def widePrefixMinimum {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (actions : List (Fin M → TargetInterval ny)) (hnonempty : actions ≠ [])
    (child : Fin M → TargetInterval ny → ℝ) (j : ℕ) (p : ℝ) : ℝ :=
  finiteMinimum (widePrefixCost parent r (actions.head hnonempty) child j p)
    (actions.map fun action => widePrefixCost parent r action child j p)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SourcePrefixes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual prefix lengths of the labeled balanced source partition. -/

namespace EditApproximation

theorem sourceChildrenList_eq_balancedPieces {α : Type*} (source : List α)
    {M : ℕ} (parent : TargetInterval source.length) :
    (List.ofFn fun i : Fin M =>
      substring source (sourceChild parent i).lo (sourceChild parent i).hi) =
        balancedPieces source parent.lo (parent.hi - parent.lo) M := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, balancedPieces_length]
  · intro i hi hj
    simp only [List.getElem_ofFn, balancedPieces, List.getElem_map, List.getElem_range, sourceChild]

theorem sourceChildren_prefix_length {α : Type*} (source : List α)
    {M : ℕ} (hM : 0 < M) (parent : TargetInterval source.length) (j : ℕ) (hj : j ≤ M) :
    ((List.ofFn fun i : Fin M =>
      substring source (sourceChild parent i).lo (sourceChild parent i).hi).take j).flatten.length =
        balancedCut parent.lo (parent.hi - parent.lo) M j - parent.lo := by
  rw [sourceChildrenList_eq_balancedPieces]
  simp only [balancedPieces, ← List.map_take, List.take_range, Nat.min_eq_left hj]
  rw [balancedPieces_prefix]
  have hcut : balancedCut parent.lo (parent.hi - parent.lo) M j ≤ source.length := by
    have h := (balancedCut_bounds parent.lo (parent.hi - parent.lo) M j hM hj).2
    rw [Nat.add_sub_of_le parent.ordered] at h
    exact h.trans parent.valid
  simp only [substring, List.length_drop, List.length_take, Nat.min_eq_left hcut]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_InitialConeGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# A rounded eligible center for each positive-cost query

This uses the actual natural division grid and the dyadic scale selected
from the integer edit cost. It supplies a finite-family witness for the
initial cone minimum.
-/

namespace EditApproximation





theorem cost_dyadicScale (c N : ℕ) (hc : 0 < c) (hcN : c ≤ N) :
    let b := 2 ^ Nat.log 2 c
    b ∈ dyadicScales N ∧ b ≤ c ∧ c < 2 * b := by
  dsimp only
  refine ⟨?_, Nat.pow_log_le_self 2 hc.ne', ?_⟩
  · apply List.mem_map.mpr
    refine ⟨Nat.log 2 c, List.mem_range.mpr ?_, rfl⟩
    exact Nat.lt_succ_of_le (Nat.log_mono_right hcN)
  · have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) c
    simpa only [pow_succ, mul_comm] using h

theorem roundInterval_on_grid {n : ℕ} (g : ℕ) (q : TargetInterval n) :
    g ∣ (roundInterval g q).lo ∧ g ∣ (roundInterval g q).hi := by
  exact ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩

theorem rounded_initial_center_numeric {c cr Ur b P A F e : ℚ}
    (hb : 0 < b) (hbc : b ≤ c) (hcb : c < 2 * b)
    (hP : 66 ≤ P) (hA : 1 ≤ A) (hF : 0 ≤ F) (he : 0 ≤ e)
    (hgrid : e * P ≤ 2 * b) (hcost : |c - cr| ≤ e)
    (hseed : cr ≤ Ur ∧ Ur ≤ A * cr) :
    b / 2 ≤ Ur ∧ Ur ≤ 4 * A * b ∧ F * cr + 32 * F * e ≤ 2 * F * c := by
  have hcosts := abs_le.mp hcost
  have hsmall : 33 * e ≤ b := by nlinarith
  have hcrlo : b / 2 ≤ cr := by linarith
  have hcrhi : cr ≤ 4 * b := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hcrhi (by linarith : 0 ≤ A)
  have hcone := mul_le_mul_of_nonneg_left (show cr + 32 * e ≤ 2 * c by linarith) hF
  exact ⟨hcrlo.trans hseed.1, hseed.2.trans (by nlinarith), by nlinarith⟩

theorem stateEditCost_distance_abs {α : Type*} (source target : List α)
    (q r : TargetInterval target.length) :
    |(stateEditCost source target q : ℚ) - stateEditCost source target r| ≤
      targetEndpointDistance q r := by
  have hqr : (stateEditCost source target q : ℚ) ≤
      stateEditCost source target r + targetEndpointDistance q r := by
    exact_mod_cast stateEditCost_spatial source target q r
  have hrq : (stateEditCost source target r : ℚ) ≤
      stateEditCost source target q + targetEndpointDistance q r := by
    have h := stateEditCost_spatial source target r q
    simpa only [targetEndpointDistance, Nat.dist_comm] using (show
      (stateEditCost source target r : ℚ) ≤ stateEditCost source target q +
        targetEndpointDistance r q by exact_mod_cast h)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Integer-computed parameters

The logarithms and fourth roots in Section 2 are computed by natural bit
lengths and nested integer square roots. No real arithmetic oracle is
used to form the algorithm's parameters.
-/

namespace EditApproximation
















theorem heightExponent_pos (N : ℕ) (hN : 0 < N) : 0 < heightExponent N := by
  apply Nat.clog_pos (by decide)
  have hlog : 1 < Nat.clog 2 (N + 2) := by
    exact (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 (by norm_num; omega)
  exact hlog

noncomputable def heightQuarterRoot (N : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (inputHeight N : ℝ))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_DomainCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Counting the actual labeled state domain

The count includes repeated interval labels at different physical nodes.
It bounds simultaneous seed/amplification events without identifying those
nodes or replacing the finite target-state loops by an oracle.
-/

namespace EditApproximation

open Finset

theorem list_flatMap_length_le {α β : Type*} (entries : List α) (f : α → List β)
    (K : ℕ) (h : ∀ a ∈ entries, (f a).length ≤ K) :
    (entries.flatMap f).length ≤ entries.length * K := by
  induction entries with
  | nil => simp
  | cons a rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have ha := h a (by simp)
    have hrest := ih (fun b hb => h b (by simp [hb]))
    nlinarith

def labeledStateCount (M nx ny : ℕ) : ℕ :=
  (∑ d ∈ range (intervalTreeDepth M nx + 1), Fintype.card (TreeLayer M d)) *
    (targetStates ny).length

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Direct enumeration of a local grid square

The algorithm enumerates bounded ranges of grid indices. It does not
scan the unrelated target positions. The completeness theorem includes
boundary states and intervals with equal endpoints.
-/

namespace EditApproximation



theorem gridPointsBetween_complete {g lo hi p : ℕ} (hg : 0 < g)
    (hlo : lo ≤ p) (hhi : p ≤ hi) (hgrid : g ∣ p) : p ∈ gridPointsBetween g lo hi := by
  have hp : g * (p / g) = p := Nat.mul_div_cancel' hgrid
  have hstart : lo ⌈/⌉ g ≤ p / g := (ceilDiv_le_iff_le_mul hg).2 (by omega)
  have hend : p / g ≤ hi / g := Nat.div_le_div_right hhi
  apply List.mem_map.mpr
  refine ⟨p / g, List.mem_range'.mpr ?_, hp⟩
  refine ⟨p / g - lo ⌈/⌉ g, by omega, ?_⟩
  omega

theorem gridPointsBetween_sound {g lo hi p : ℕ} (hg : 0 < g)
    (hp : p ∈ gridPointsBetween g lo hi) : lo ≤ p ∧ p ≤ hi ∧ g ∣ p := by
  obtain ⟨i, hmem, rfl⟩ := List.mem_map.mp hp
  obtain ⟨j, hj, rfl⟩ := List.mem_range'.mp hmem
  have hstart : lo ≤ g * (lo ⌈/⌉ g) := (ceilDiv_le_iff_le_mul hg).mp le_rfl
  have hindex : lo ⌈/⌉ g + 1 * j ≤ hi / g := by omega
  have hfinish := Nat.mul_div_le hi g
  exact ⟨by nlinarith, (Nat.mul_le_mul_left g hindex).trans hfinish, dvd_mul_right _ _⟩

theorem gridPointsBetween_length (g lo hi : ℕ) :
    (gridPointsBetween g lo hi).length = (hi / g + 1) - lo ⌈/⌉ g := by
  simp only [gridPointsBetween, List.length_map, List.length_range']

theorem gridPointsBetween_length_le (g lo hi : ℕ) (hg : 0 < g) :
    (gridPointsBetween g lo hi).length ≤ (hi - lo) / g + 2 := by
  rw [gridPointsBetween_length]
  have hceil : lo ≤ g * (lo ⌈/⌉ g) := (ceilDiv_le_iff_le_mul hg).mp le_rfl
  have hfloor : lo / g ≤ lo ⌈/⌉ g := by
    have hdiv := Nat.div_le_div_right (c := g) hceil
    simpa only [Nat.mul_div_right _ hg] using hdiv
  by_cases horder : lo ≤ hi
  · have hlo := Nat.lt_mul_div_succ lo hg
    have hdiff := Nat.lt_mul_div_succ (hi - lo) hg
    have hsplit : lo + (hi - lo) = hi := Nat.add_sub_of_le horder
    have hdiv : hi / g < lo / g + (hi - lo) / g + 2 := by
      apply (Nat.div_lt_iff_lt_mul hg).2
      nlinarith
    apply Nat.sub_le_of_le_add
    calc
      hi / g + 1 ≤ lo / g + (hi - lo) / g + 2 := hdiv
      _ ≤ (lo ⌈/⌉ g) + (hi - lo) / g + 2 := by gcongr
      _ = (hi - lo) / g + 2 + lo ⌈/⌉ g := by omega
  · have hmono := Nat.div_le_div_right (c := g) (by omega : hi ≤ lo)
    have hshort : hi / g + 1 - lo ⌈/⌉ g ≤ 1 := Nat.sub_le_of_le_add (by omega)
    exact hshort.trans ((by decide : 1 ≤ 2).trans (Nat.le_add_left 2 _))



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteAssignments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Executable finite products of child-state lists

The wide-action lists use this literal recursive Cartesian product.
Their coordinates are child labels, so duplicate interval labels remain
distinct coordinates.
-/

namespace EditApproximation



theorem finiteAssignments_complete {α : Type*} (M : ℕ) (choices : Fin M → List α)
    (action : Fin M → α) (ha : ∀ i, action i ∈ choices i) :
    action ∈ finiteAssignments M choices := by
  induction M with
  | zero =>
    have haction : action = Fin.elim0 := by funext i; exact Fin.elim0 i
    simp only [finiteAssignments, haction, List.mem_singleton]
  | succ M ih =>
    apply List.mem_flatMap.mpr
    refine ⟨action 0, ha 0, List.mem_map.mpr ?_⟩
    refine ⟨fun i => action i.succ, ih _ _ (fun i => ha i.succ), ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem finiteAssignments_sound {α : Type*} (M : ℕ) (choices : Fin M → List α)
    (action : Fin M → α) (ha : action ∈ finiteAssignments M choices) :
    ∀ i, action i ∈ choices i := by
  induction M with
  | zero => intro i; exact Fin.elim0 i
  | succ M ih =>
    obtain ⟨head, hhead, hrest⟩ := List.mem_flatMap.mp ha
    obtain ⟨tail, htail, rfl⟩ := List.mem_map.mp hrest
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hhead
    · exact ih _ _ htail _

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_WideActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Executable wide action lists

Endpoint indices are generated in the radius-`10b` grid boxes anchored
at the physical source cuts. Lists contain exactly the valid grid states
in those boxes and their Cartesian product over labeled children.
-/

namespace EditApproximation



theorem gridStateBox_length_le (n g radius lo hi : ℕ) (hg : 0 < g) :
    (gridStateBox n g radius lo hi).length ≤ (2 * radius / g + 2) ^ 2 := by
  have hpoint (p : ℕ) :
      (gridPointsBetween g (p - radius) (p + radius)).length ≤ 2 * radius / g + 2 := by
    have hlength := gridPointsBetween_length_le g (p - radius) (p + radius) hg
    have hwidth : p + radius - (p - radius) ≤ 2 * radius := by omega
    exact hlength.trans (Nat.add_le_add_right (Nat.div_le_div_right hwidth) 2)
  have hlist := list_flatMap_length_le
    (gridPointsBetween g (lo - radius) (lo + radius))
    (fun s => (gridPointsBetween g (hi - radius) (hi + radius)).filterMap
      fun t => makeTargetState n s t)
    (2 * radius / g + 2) (by intro s hs; exact (List.length_filterMap_le _ _).trans (hpoint hi))
  exact hlist.trans (by simpa only [pow_two] using
    (Nat.mul_le_mul_right (2 * radius / g + 2) (hpoint lo)))





theorem seedGridSpacing_radius_count (b P : ℕ) (hP : 0 < P) :
    20 * b / seedGridSpacing b P + 2 ≤ 40 * P + 2 := by
  let g := seedGridSpacing b P
  have hg : 0 < g := by unfold g seedGridSpacing; omega
  have hg1 : 1 ≤ g := hg
  have hquot : b / P ≤ g := le_max_right _ _
  have hdiv := Nat.lt_mul_div_succ b hP
  have hprod : b < 2 * P * g := by nlinarith
  have hscale : 20 * b < (40 * P + 1) * g := by nlinarith
  have hresult := (Nat.div_lt_iff_lt_mul hg).2 hscale
  change 20 * b / g + 2 ≤ 40 * P + 2
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PrefixComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual comparison prefixes in the finite wide action family

The cut is the start of the remaining comparator suffix, or the parent's
end when that suffix is empty. Splitting at this cut preserves the literal
connection budget. Splicing any enumerated prefix to the comparator suffix
remains an enumerated wide action.
-/

namespace EditApproximation

open Finset

def connectionPrefixBoundary {n : ℕ} (states : List (TargetInterval n)) (finish j : ℕ) : ℕ :=
  ((states.drop j).head?.map TargetInterval.lo).getD finish

def comparisonPrefixSplice {n M : ℕ} (before comparison : Fin M → TargetInterval n)
    (j : ℕ) : Fin M → TargetInterval n := fun i => if i.val < j then before i else comparison i

noncomputable def comparisonPrefixShift {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (comparison : Fin M → TargetInterval ny) (j : ℕ) : ℝ :=
  (connectionPrefixBoundary (List.ofFn comparison) r.hi j : ℝ) -
    balancedCut parent.lo (parent.hi - parent.lo) M j

noncomputable def comparisonPrefixValue {ny M : ℕ} (comparison : Fin M → TargetInterval ny)
    (child : Fin M → TargetInterval ny → ℝ) (j : ℕ) : ℝ :=
  ∑ i, if i.val < j then child i (comparison i) else 0

/-- Real form of the literal local wide-action minimum; the first member
is duplicated as fallback, exactly as in the rational predictor. -/
noncomputable def wideActionMinimum {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (hnonempty : wideActionList M parent r b P ≠ [])
    (child : Fin M → TargetInterval ny → ℝ) : ℝ :=
  finiteMinimum (endpointActionValue r ((wideActionList M parent r b P).head hnonempty) child)
    ((wideActionList M parent r b P).map fun action => endpointActionValue r action child)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Bands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Predicted-band geometry

The prefix-cost predictor is 1-Lipschitz, while its velocity has a strict
margin below one. This gives narrow bands without a convexity assumption
on the set of allowed endpoints (Sections 5 and 6 of the manuscript).
-/

namespace EditApproximation

def inPredictedBand (prefixCost : ℝ → ℝ) (origin velocity margin width point : ℝ) : Prop :=
  |point - origin - velocity * prefixCost point| ≤ margin * width

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite uniform sampling

The shared group estimator samples child labels uniformly with replacement.
These lemmas use that finite distribution, including its product law;
they do not assume that different group representatives are independent.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

noncomputable def uniformMean {ι : Type*} [Fintype ι] (value : ι → ℝ) : ℝ :=
  (∑ i, value i) / Fintype.card ι

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GroupSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Shared group sampling

The one-scale estimator in Section 5 is a finite uniform average. Its
concentration follows from the explicitly cited Bernstein input. Choosing
among representatives and extending their costs by cones is deterministic
on the simultaneous approximation event, even when their samples are shared.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

noncomputable def normalizedChildSample {M : ℕ} (b h : ℝ)
    (childScale childValue : Fin M → ℝ) (i : Fin M) : ℝ :=
  if childScale i = h then (M : ℝ) * childValue i / b else 0

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonBandCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Comparison action coverage by the computed predictor

Masses, gaps, prefix costs and curvature are those of the actual labeled
comparison action. The finite wide-action minimum supplies Z. No scalar
prefix prediction contract is assumed.
-/

namespace EditApproximation

open Finset

noncomputable def comparisonActionMass {ny M : ℕ}
    (comparison : Fin M → TargetInterval ny) (child : Fin M → TargetInterval ny → ℝ) : ℝ :=
  ∑ i, child i (comparison i)

noncomputable def comparisonActionCurvature {α : Type*} (source target : List α)
    {M : ℕ} (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (comparison : Fin M → TargetInterval target.length)
    (child : Fin M → TargetInterval target.length → ℝ) : ℝ :=
  (∑ i, (stateLengthGap
    (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (comparison i)) ^ 2 /
      child i (comparison i)) -
    (stateLengthGap (substring source parent.lo parent.hi) target r) ^ 2 /
      comparisonActionMass comparison child

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_StateDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The actual finite labeled state type

Physical nodes are retained as depth/path pairs. In particular, repeated
empty intervals remain distinct entries of the seed and refinement tables.
-/

namespace EditApproximation

open Finset





abbrev LabeledEntry (M nx ny : ℕ) :=
  PhysicalNode M (intervalTreeDepth M nx) × TargetInterval ny

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandGroupSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Executable shared group estimates

All dyadic powers in the prescribed closed range are enumerated, including
negative exponents. A scale is evaluated exactly when its sample count
reaches the child count; otherwise one shared array of uniform labels is
used for every member of the group. The selected member is the first
minimizer in the fixed list order.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory



/-- Fixed ordered minimization; negating the rational estimate turns the
finite maximum operation into the first cost minimum. -/


theorem selectGroupMember_spec {ι : Type*} (members : List ι) (hnonempty : members ≠ [])
    (estimate : ι → ℚ) :
    selectGroupMember members hnonempty estimate ∈ members ∧
      ∀ member ∈ members, estimate (selectGroupMember members hnonempty estimate) ≤ estimate member := by
  unfold selectGroupMember
  cases harg : members.argmax (fun member => -estimate member) with
  | none => exact False.elim (hnonempty (List.argmax_eq_none.mp harg))
  | some selected =>
    simp only [Option.getD_some]
    have hmem : selected ∈ members.argmax (fun member => -estimate member) := by rw [harg]; simp
    refine ⟨List.argmax_mem hmem, ?_⟩
    intro member hmember
    have h := List.le_of_mem_argmax (f := fun member => -estimate member) hmember hmem
    linarith

noncomputable def groupSharedDrawLaw {M T : ℕ} [NeZero M]
    [MeasurableSpace (Fin M)] (count : Fin T → ℕ) :
    Measure (∀ scale : Fin T, Fin (count scale) → Fin M) :=
  Measure.pi fun scale : Fin T =>
    Measure.pi fun _ : Fin (count scale) => (PMF.uniformOfFintype (Fin M)).toMeasure

instance groupSharedDrawLaw_isProbabilityMeasure {M T : ℕ} [NeZero M]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] (count : Fin T → ℕ) :
    IsProbabilityMeasure (groupSharedDrawLaw (M := M) count) := by
  unfold groupSharedDrawLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

section ActualUnskippedGroup

variable {α : Type*} {source target : List α} {M b P thetaExponent : ℕ}
  {parent : TargetInterval source.length} {tau F : ℚ}
  {child initial : Fin M → TargetInterval target.length → ℚ}

theorem testUnskippedBand_center
    (center : TargetInterval target.length)
    (member : UnskippedBand source target parent b P thetaExponent tau F child initial)
    (haccepted : testUnskippedBand source target parent b P thetaExponent tau F child initial center = some member) :
    member.center = center := by
  unfold testUnskippedBand at haccepted
  dsimp only at haccepted
  split_ifs at haccepted
  cases haccepted
  rfl



theorem chooseUnskippedGroup_spec (Q : ℕ)
    (value : Fin M → TargetInterval target.length → ℚ)
    (members : List (UnskippedBand source target parent b P thetaExponent tau F child initial))
    (hnonempty : members ≠ [])
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M) :
    chooseUnskippedGroup Q value members hnonempty draw ∈ members ∧
      ∀ member ∈ members,
        dyadicUnskippedGroupEstimate Q value (chooseUnskippedGroup Q value members hnonempty draw) draw ≤
          dyadicUnskippedGroupEstimate Q value member draw :=
  selectGroupMember_spec members hnonempty (fun member => dyadicUnskippedGroupEstimate Q value member draw)


end ActualUnskippedGroup

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dimension charged by entropy is the number of actual child coordinates. -/

namespace EditApproximation

open Finset

theorem wideChildStateList_length_le {nx ny M b P : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (hP : 0 < P) (i : Fin M) :
    (wideChildStateList parent r b P i).length ≤ (40 * P + 2) ^ 2 := by
  have h := gridStateBox_length_le ny (seedGridSpacing b P) (10 * b)
    (r.lo + ((sourceChild parent i).lo - parent.lo))
    (r.lo + ((sourceChild parent i).hi - parent.lo)) (by unfold seedGridSpacing; omega)
  exact h.trans (Nat.pow_le_pow_left (by
    simpa only [show 2 * (10 * b) = 20 * b by omega] using seedGridSpacing_radius_count b P hP) 2)

theorem bandCoordinates_card_le {nx ny M b P : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (hP : 0 < P) (band : List (Fin M → TargetInterval ny))
    (hband : ∀ action ∈ band, action ∈ wideActionList M parent r b P) :
    (bandCoordinates band.toFinset).card ≤ M * (40 * P + 2) ^ 2 := by
  classical
  let coordinateSet := univ.biUnion fun i : Fin M =>
    (wideChildStateList parent r b P i).toFinset.image fun s => (i, s)
  have hsub : bandCoordinates band.toFinset ⊆ coordinateSet := by
    intro coordinate hcoordinate
    obtain ⟨action, ha, hcoord⟩ := mem_biUnion.mp hcoordinate
    obtain ⟨i, _, rfl⟩ := mem_image.mp hcoord
    apply mem_biUnion.mpr
    refine ⟨i, mem_univ _, mem_image.mpr ⟨action i, ?_, rfl⟩⟩
    exact List.mem_toFinset.mpr (finiteAssignments_sound M _ action
      (hband action (List.mem_toFinset.mp ha)) i)
  have hsum : coordinateSet.card ≤ ∑ i : Fin M, (40 * P + 2) ^ 2 := by
    apply (card_biUnion_le).trans
    apply sum_le_sum
    intro i _
    exact (card_image_le).trans ((List.toFinset_card_le _).trans
      (wideChildStateList_length_le parent r hP i))
  exact (card_le_card hsub).trans (by simpa only [sum_const, card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul] using hsum)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandOptimizerWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Reindexing the exact finite optimizer onto an explicit, duplicate-free
coordinate array. The array order is retained throughout the evaluation. -/

namespace EditApproximation

open Finset

def restrictOptimizerVector {ι : Type*} {d : ℕ} (coordinates : Vector ι d)
    (values : ι → ℚ) : Vector ℚ d :=
  Vector.ofFn fun i => values (coordinates.get i)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ConeLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The numerical locality test for initial cones

Any globally minimizing cone at a positive-cost query lies in the
algorithm's finite local scale interval and search radius. The inequalities
below use the actual seed factor and cone slope from Section 4.
-/

namespace EditApproximation

theorem initial_cone_locality_numeric {c centerCost Uq Ur distance b A F cone : ℚ}
    (hc : 0 < c) (hA : 1 ≤ A) (hF : 0 < F) (hb : 0 ≤ b)
    (hquery : c ≤ Uq ∧ Uq ≤ A * c)
    (hcenter : centerCost ≤ Ur ∧ Ur ≤ A * centerCost)
    (hcost : |c - centerCost| ≤ distance)
    (heligible : b / 2 ≤ Ur ∧ Ur ≤ 4 * A * b)
    (hconeLower : 32 * F * distance ≤ cone) (hconeUpper : cone ≤ 2 * F * c) :
    distance ≤ c / 16 ∧ Ur ≠ 0 ∧ Uq / (16 * A ^ 2) ≤ b ∧ b ≤ 4 * A * Uq ∧ distance ≤ Uq := by
  have hA0 : 0 < A := by linarith
  have hdist : distance ≤ c / 16 := by
    have hscaled : F * (16 * distance - c) ≤ 0 := by nlinarith
    have hdiff : 16 * distance - c ≤ 0 := by nlinarith
    linarith
  have hcosts := abs_le.mp hcost
  have hcrLower : c / 2 ≤ centerCost := by linarith
  have hcrUpper : centerCost ≤ 2 * c := by linarith
  have hUrpos : 0 < Ur := by linarith [hcenter.1]
  have hcScale : c ≤ 8 * A * b := by linarith [hcenter.1, heligible.2]
  have hAc := mul_le_mul_of_nonneg_left hcScale hA0.le
  have hAb : 0 ≤ A ^ 2 * b := mul_nonneg (sq_nonneg _) hb
  have hlower : Uq / (16 * A ^ 2) ≤ b := by
    apply (div_le_iff₀ (by positivity : 0 < 16 * A ^ 2)).2
    nlinarith [hquery.2]
  have hcenterScale := mul_le_mul_of_nonneg_left hcrUpper hA0.le
  have hqueryScale := mul_le_mul_of_nonneg_left hquery.1 (by positivity : 0 ≤ 4 * A)
  have hupper : b ≤ 4 * A * Uq := by nlinarith [heligible.1, hcenter.2]
  exact ⟨hdist, hUrpos.ne', hlower, hupper, by linarith [hquery.1]⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_InitialConeTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite global initial-cone table

Every center is a valid target state. The family includes the zero seed
centers and precisely the eligible grid centers at the finite dyadic scales.
The constant fallback is above a witnessed cone on a good seed.
-/

namespace EditApproximation

def initialConeCenters {n : ℕ} (N P : ℕ) (A : ℚ) (U : TargetInterval n → ℕ) :
    List (TargetInterval n) :=
  (targetStates n).filter (fun r => decide (U r = 0)) ++
  (dyadicScales N).flatMap (fun b =>
    (targetStates n).filter (fun r => decide
      (seedGridSpacing b P ∣ r.lo ∧ seedGridSpacing b P ∣ r.hi ∧
        (b : ℚ) / 2 ≤ U r ∧ (U r : ℚ) ≤ 4 * A * b)))

def globalInitialConeTable {α : Type*} (source target : List α)
    (U : TargetInterval target.length → ℕ) (N P F : ℕ) (A a : ℚ)
    (q : TargetInterval target.length) : ℚ :=
  rationalMinimum ((32 * F + 1) * N)
    ((initialConeCenters N P A U).map (initialConeValue source target U a (32 * F) q))

theorem rationalMinimum_le_member (fallback : ℚ) (values : List ℚ)
    {v : ℚ} (hv : v ∈ values) : rationalMinimum fallback values ≤ v := by
  induction values with
  | nil => simp at hv
  | cons x rest ih =>
    rcases List.mem_cons.mp hv with rfl | hrest
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hrest)

theorem le_rationalMinimum_iff (lower fallback : ℚ) (values : List ℚ) :
    lower ≤ rationalMinimum fallback values ↔ lower ≤ fallback ∧ ∀ v ∈ values, lower ≤ v := by
  induction values with
  | nil => simp [rationalMinimum]
  | cons v rest ih =>
    simp only [rationalMinimum, le_min_iff, ih, List.mem_cons, forall_eq_or_imp]
    tauto

theorem targetEndpointDistance_triangle {n : ℕ} (q q' r : TargetInterval n) :
    targetEndpointDistance q r ≤ targetEndpointDistance q' r + targetEndpointDistance q q' := by
  unfold targetEndpointDistance Nat.dist
  omega

theorem globalInitialConeTable_spatial {α : Type*} (source target : List α)
    (U : TargetInterval target.length → ℕ) (N P F : ℕ) (A a : ℚ)
    (q q' : TargetInterval target.length) :
    globalInitialConeTable source target U N P F A a q ≤
      globalInitialConeTable source target U N P F A a q' +
        (32 * F : ℚ) * targetEndpointDistance q q' := by
  have hcast (query : TargetInterval target.length) :
      (globalInitialConeTable source target U N P F A a query : ℝ) =
        finiteMinimum (((32 * F + 1) * N : ℚ) : ℝ)
          ((initialConeCenters N P A U).map
            fun r => (initialConeValue source target U a (32 * F) query r : ℝ)) := by
    rw [globalInitialConeTable, rationalMinimum_cast]
    simp only [List.map_map, Function.comp_def]
  have h := finiteMinimum_map_spatial (initialConeCenters N P A U)
    (((32 * F + 1) * N : ℚ) : ℝ) (((32 * F + 1) * N : ℚ) : ℝ)
    (((32 * F : ℚ) * targetEndpointDistance q q' : ℚ) : ℝ)
    (fun r => (initialConeValue source target U a (32 * F) q r : ℝ))
    (fun r => (initialConeValue source target U a (32 * F) q' r : ℝ))
    (le_add_of_nonneg_right (by positivity)) (by
      intro r hr
      have htri : (targetEndpointDistance q r : ℚ) ≤
          targetEndpointDistance q' r + targetEndpointDistance q q' := by
        exact_mod_cast targetEndpointDistance_triangle q q' r
      have hmult := mul_le_mul_of_nonneg_left htri (by positivity : (0 : ℚ) ≤ 32 * F)
      have hcone : initialConeValue source target U a (32 * F) q r ≤
          initialConeValue source target U a (32 * F) q' r +
            (32 * F : ℚ) * targetEndpointDistance q q' := by
        unfold initialConeValue
        linarith
      exact_mod_cast hcone)
  rw [← hcast q, ← hcast q'] at h
  exact_mod_cast h

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalInitialCones
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Exact local evaluation of the initial cones

The local implementation enumerates only the stated dyadic scale interval
and the grid square about the query. Zero cones are never searched at a
positive seed query. Equality with the global family is proved on a good
seed; the local program is finite on every input table.
-/

namespace EditApproximation





theorem rationalMinimum_le_fallback (fallback : ℚ) (values : List ℚ) :
    rationalMinimum fallback values ≤ fallback := by
  induction values with
  | nil => rfl
  | cons v rest ih => exact (min_le_right _ _).trans ih

theorem rationalMinimum_attained (fallback : ℚ) (values : List ℚ) :
    rationalMinimum fallback values = fallback ∨ rationalMinimum fallback values ∈ values := by
  induction values with
  | nil => exact Or.inl rfl
  | cons v rest ih =>
    by_cases h : v ≤ rationalMinimum fallback rest
    · exact Or.inr (by simp only [rationalMinimum, min_eq_left h, List.mem_cons, true_or])
    · rw [rationalMinimum, min_eq_right (le_of_not_ge h)]
      exact ih.imp_right (fun hmem => List.mem_cons.mpr (Or.inr hmem))

theorem localTargetStates_on_grid {n g radius : ℕ} (q r : TargetInterval n)
    (hmem : r ∈ localTargetStates n g radius q) : g ∣ r.lo ∧ g ∣ r.hi := by
  obtain ⟨lo, hlo, hrest⟩ := List.mem_flatMap.mp hmem
  obtain ⟨hi, hhi, hmake⟩ := List.mem_filterMap.mp hrest
  unfold makeTargetState at hmake
  split at hmake
  · cases Option.some.inj hmake
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hlo
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hhi
    exact ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩
  · contradiction

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalWarmup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Warmup on physical node labels

The Bellman operator requests only physical children. Distinct child labels
are retained even at repeated cuts. Nodes at the last physical level, and
source intervals of width at most one, retain their initial value.
-/

namespace EditApproximation









noncomputable def physicalLower {α : Type*} {M J : ℕ} (source target : List α) (a : ℝ)
    (state : PhysicalEntry M J target.length) : ℝ :=
  max ((stateEditCost (physicalSource source state.1) target state.2 : ℝ) / a)
    |stateLengthGap (physicalSource source state.1) target state.2|

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GroupCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Whole rational cells are enumerated by bounded ranges of grid indices. -/

namespace EditApproximation



theorem cellGridPoints_mem {side : ℚ} {g cell p : ℕ} (hg : 0 < g) :
    p ∈ cellGridPoints side g cell ↔
      g ∣ p ∧ (cell : ℚ) * side ≤ p ∧ (p : ℚ) < ((cell : ℚ) + 1) * side := by
  have hgr : (0 : ℚ) < g := by exact_mod_cast hg
  constructor
  · intro hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    obtain ⟨j, hj, rfl⟩ := List.mem_range'.mp hi
    have hlo : ⌈(cell : ℚ) * side / g⌉₊ ≤ ⌈(cell : ℚ) * side / g⌉₊ + 1 * j := by omega
    have hhi : ⌈(cell : ℚ) * side / g⌉₊ + 1 * j < ⌈((cell : ℚ) + 1) * side / g⌉₊ := by omega
    have hloR := (Nat.ceil_le.mp hlo)
    have hhiR := (Nat.lt_ceil.mp hhi)
    refine ⟨dvd_mul_right _ _, ?_, ?_⟩
    · have h := (div_le_iff₀ hgr).mp hloR
      push_cast at h
      push_cast
      simpa only [mul_comm] using h
    · have h := (lt_div_iff₀ hgr).mp hhiR
      push_cast at h
      push_cast
      simpa only [mul_comm] using h
  · rintro ⟨hgrid, hlo, hhi⟩
    have heq : g * (p / g) = p := Nat.mul_div_cancel' hgrid
    have hloR : (cell : ℚ) * side / g ≤ (p / g : ℕ) := by
      apply (div_le_iff₀ hgr).2
      have hc : (g : ℚ) * (p / g : ℕ) = p := by exact_mod_cast heq
      linarith only [hlo, hc]
    have hhiR : ((p / g : ℕ) : ℚ) < ((cell : ℚ) + 1) * side / g := by
      apply (lt_div_iff₀ hgr).2
      have hc : (g : ℚ) * (p / g : ℕ) = p := by exact_mod_cast heq
      linarith only [hhi, hc]
    have hstart := Nat.ceil_le.mpr hloR
    have hend := Nat.lt_ceil.mpr hhiR
    apply List.mem_map.mpr
    refine ⟨p / g, List.mem_range'.mpr ?_, heq⟩
    exact ⟨p / g - ⌈(cell : ℚ) * side / g⌉₊, by omega, by omega⟩

def targetCell {n : ℕ} (side : ℚ) (q : TargetInterval n) : ℕ × ℕ :=
  (⌊(q.lo : ℚ) / side⌋₊, ⌊(q.hi : ℚ) / side⌋₊)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_CellGroupSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal unskipped groups of whole cells and their selected wide actions. -/

namespace EditApproximation

open Finset



namespace UnskippedBand

theorem canonicalRounded_congr {ny M : ℕ} (thetaExponent b : ℕ)
    (band band' : List (Fin M → TargetInterval ny)) (heq : band = band')
    (hnonempty : band ≠ []) (hnonempty' : band' ≠ [])
    (initial : Fin M → TargetInterval ny → ℚ) :
    canonicalRoundedBandAction thetaExponent b band hnonempty initial =
      canonicalRoundedBandAction thetaExponent b band' hnonempty' initial := by
  cases heq
  rfl



theorem rationalAction_wide_mem {α : Type*} {source target : List α} {M b P thetaExponent : ℕ}
    {parent : TargetInterval source.length} {tau F : ℚ}
    {child initial : Fin M → TargetInterval target.length → ℚ}
    (member : UnskippedBand source target parent b P thetaExponent tau F child initial)
    (representatives : List (ℕ × TargetInterval target.length)) (hrep : (b, member.center) ∈ representatives) :
    member.rationalAction ∈ rationalActualWideActions parent representatives P := by
  apply List.mem_flatMap.mpr
  exact ⟨(b, member.center), hrep, List.mem_map.mpr ⟨member.rounded, member.wide_guard, rfl⟩⟩

end UnskippedBand



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_Exact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# An executable exact cut recurrence

This is the exact source-cut dynamic programming recurrence on ordinary
lists and natural numbers. The proof identifies its value with unrestricted
unit-cost edit distance. Storage and evaluation costs are separate from
this value-level recurrence.
-/

namespace EditApproximation

open EditDistortion

theorem edit_nil_left {α : Type*} (target : List α) : edit [] target = target.length := by
  have hlo := (cost_length_bounds (s := true) ([] : List α) target).2
  have hup := cost_le (Script.to_nil (s := true) target).symm
  change edit [] target ≤ target.length at hup
  change target.length ≤ 0 + edit [] target at hlo
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The actual initial table uses exact empty/singleton leaves and local cones elsewhere. -/

namespace EditApproximation

open EditDistortion



theorem physicalSource_length_le {α : Type*} {M J : ℕ} (source : List α)
    (node : PhysicalNode M J) : (physicalSource source node).length ≤ source.length := by
  simp only [physicalSource, substring, List.length_drop, List.length_take]
  exact (Nat.sub_le _ _).trans (min_le_right _ _)

theorem physical_state_cost_le {α : Type*} {M J : ℕ} (source target : List α)
    (N : ℕ) (hsize : source.length + target.length ≤ N)
    (state : PhysicalEntry M J target.length) :
    stateEditCost (physicalSource source state.1) target state.2 ≤ N := by
  apply (edit_le_max_length _ _).trans
  apply max_le
  · exact (physicalSource_length_le source state.1).trans (by omega)
  · have hlen : (substring target state.2.lo state.2.hi).length ≤ target.length := by
      simp only [substring, List.length_drop, List.length_take]
      exact (Nat.sub_le _ _).trans (min_le_right _ _)
    exact hlen.trans (by omega)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageWarmup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The literal initial table, representative enumeration and rational warmup of one refinement pass. -/

namespace EditApproximation



theorem refinementFactor_spec (A : ℚ) (F : ℕ) (hF : 0 < F) :
    1 ≤ refinementFactor A F ∧ A ≤ refinementFactor A F * F := by
  have hFr : (0 : ℚ) < F := by exact_mod_cast hF
  refine ⟨le_max_left _ _, ?_⟩
  have h := mul_le_mul_of_nonneg_right (le_max_right (1 : ℚ) (A / F)) hFr.le
  rw [div_mul_cancel₀ _ hFr.ne'] at h
  exact h

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalBoundsAllSeeds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonnegativity and size bounds hold on every seed and every sample outcome. -/

namespace EditApproximation

open Finset

theorem rationalActualWideActions_connection_nonneg {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (action : PhysicalRationalAction M ny)
    (ha : action ∈ rationalActualWideActions parent representatives P) : 0 ≤ action.connection := by
  obtain ⟨br, _, hmem⟩ := List.mem_flatMap.mp ha
  obtain ⟨states, _, rfl⟩ := List.mem_map.mp hmem
  exact Nat.cast_nonneg _

theorem localInitialConeTable_nonneg {α : Type*} (source target : List α)
    (U : TargetInterval target.length → ℕ) (N P F : ℕ) (A a : ℚ) (q : TargetInterval target.length) :
    0 ≤ localInitialConeTable source target U N P F A a q := by
  unfold localInitialConeTable
  split_ifs
  · exact le_rfl
  · apply (le_rationalMinimum_iff _ _ _).2
    refine ⟨by positivity, ?_⟩
    intro v hv
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hv
    unfold initialConeValue scaledSeedValue
    positivity

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_RationalPruning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact candidate pruning uses value lower bounds, without an accuracy event. -/

namespace EditApproximation

open Finset

theorem rationalMinimum_local_complete {ι : Type*} (complete nearby : List ι)
    (value : ι → ℚ) (fallback : ℚ)
    (hsubset : ∀ i ∈ nearby, i ∈ complete)
    (hcover : ∀ i ∈ complete, value i ≤ fallback → i ∈ nearby) :
    rationalMinimum fallback (nearby.map value) = rationalMinimum fallback (complete.map value) := by
  apply le_antisymm
  · apply (le_rationalMinimum_iff _ _ _).2
    refine ⟨rationalMinimum_le_fallback _ _, ?_⟩
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    by_cases hvalue : value i ≤ fallback
    · exact rationalMinimum_le_member _ _ (List.mem_map.mpr ⟨i, hcover i hi hvalue, rfl⟩)
    · exact (rationalMinimum_le_fallback _ _).trans (le_of_not_ge hvalue)
  · apply (le_rationalMinimum_iff _ _ _).2
    refine ⟨rationalMinimum_le_fallback _ _, ?_⟩
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    exact rationalMinimum_le_member _ _ (List.mem_map.mpr ⟨i, hsubset i hi, rfl⟩)

theorem rationalActionValue_pruned_lower {Parent Child : Type*} {M : ℕ}
    (distance : Parent → Parent → ℚ) (L : ℚ) (child : Child → ℚ) (q : Parent)
    (action : RationalBellmanAction Parent Child M) (threshold : ℚ)
    (hcharge : threshold ≤ L * distance q action.center)
    (hconnection : 0 ≤ action.connection) (hchild : ∀ i, 0 ≤ child (action.childState i)) :
    threshold ≤ rationalActionValue distance L child q action := by
  unfold rationalActionValue
  apply hcharge.trans
  simpa only [add_assoc] using
    (le_add_of_nonneg_right (a := L * distance q action.center)
      (add_nonneg hconnection (sum_nonneg fun i _ => hchild i)))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RefinementConeLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Good-seed equality with the finite local scale and center rule. -/

namespace EditApproximation

theorem refinement_cone_locality_numeric {w wr distance b a F cone : ℚ}
    (hw : 0 < w) (ha : 1 ≤ a) (hF : 1 ≤ F) (hdistance : 0 ≤ distance)
    (hspatial : |w - wr| ≤ 32 * F * distance)
    (heligible : b / (4 * a) ≤ wr ∧ wr ≤ 8 * F * b)
    (hconeLower : 128 * F * distance ≤ cone) (hconeUpper : cone ≤ w) :
    w / (16 * F) ≤ b ∧ b ≤ 8 * a * w ∧ distance ≤ w := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hF0 : 0 < F := lt_of_lt_of_le zero_lt_one hF
  have hnear : 32 * F * distance ≤ w / 4 := by nlinarith only [hconeLower, hconeUpper]
  have hdiff := abs_le.mp hspatial
  have hwrLower : 3 * w / 4 ≤ wr := by linarith only [hdiff.2, hnear]
  have hwrUpper : wr ≤ 5 * w / 4 := by linarith only [hdiff.1, hnear]
  have hlower : w / (16 * F) ≤ b := by
    apply (div_le_iff₀ (by positivity : 0 < 16 * F)).2
    nlinarith only [hwrLower, heligible.2, hw.le]
  have hb : b ≤ wr * (4 * a) := (div_le_iff₀ (by positivity : 0 < 4 * a)).1 heligible.1
  have hmul := mul_le_mul_of_nonneg_right hwrUpper (show 0 ≤ 4 * a by positivity)
  have hupper : b ≤ 8 * a * w := by nlinarith only [hb, hmul, mul_nonneg ha0.le hw.le]
  have hdist : distance ≤ 128 * F * distance := by
    have hm := mul_le_mul_of_nonneg_right hF hdistance
    nlinarith only [hm, hdistance]
  exact ⟨hlower, hupper, hdist.trans (hconeLower.trans hconeUpper)⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalRefinementCones
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Direct local enumeration computes the complete refinement Bellman cone
on a spatially regular initial table. Its finite definition applies to every seed. -/

namespace EditApproximation

open Finset



theorem rationalActualWideActions_mono {nx ny M : ℕ}
    (parent : TargetInterval nx) (complete nearby : List (ℕ × TargetInterval ny)) (P : ℕ)
    (hsubset : ∀ br ∈ nearby, br ∈ complete) :
    ∀ action ∈ rationalActualWideActions (M := M) parent nearby P,
      action ∈ rationalActualWideActions parent complete P := by
  intro action ha
  obtain ⟨br, hbr, ha⟩ := List.mem_flatMap.mp ha
  exact List.mem_flatMap.mpr ⟨br, hsubset br hbr, ha⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_FirstCrossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual first crossing of a finite action band

The crossing index is computed from the fixed child tables for analysis.
It is independent of parent sampling. The lemmas separate the prefixPayoff,
the single crossing, and the nonpositive later clipped regrets.
-/

namespace EditApproximation

open Finset

noncomputable def firstCrossing {α : Type*} (band : Finset α)
    (S : ℕ) (actionCost : ℕ → α → ℝ) (c : ℝ) : ℕ :=
  if h : ∃ t, t < S ∧ ∃ action ∈ band, actionCost t action < c then Nat.find h else S

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_NodeRegret
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Clipped regret of the actual refinement update

This is the deterministic first-crossing transfer in Proposition 7.3.
The hypothesis about group estimates is a pointwise estimate on their
success event; their probability is handled separately. No independence
between a sampled action and that success event is required.
-/

namespace EditApproximation

open Finset

noncomputable def bandActionCost {β σ : Type*} [Fintype β]
    (charge : ℝ) (table : ℕ → β × σ → ℝ) (t : ℕ) (action : β → σ) : ℝ :=
  charge + ∑ child, table t (child, action child)

noncomputable def sampledPrefixRegret {β σ : Type*} [Fintype β]
    (charge κ : ℝ) (table : ℕ → β × σ → ℝ)
    (comparisonClipped : ℕ → ℝ) (sample : ℕ → β → σ) (t : ℕ) : ℝ :=
  bandActionCost charge table (t + 1) (sample t) +
    κ * (bandActionCost charge table t (sample t) -
      bandActionCost charge table (t + 1) (sample t)) - charge - comparisonClipped (t + 1)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalNodeRegret
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# First crossing for the literal physical refinement

Online and selected-group candidates are connected to the complete
refinement by membership in its actual finite lists. Group success is the
literal simultaneous estimator-error test, rather than a cone-bound
assumption. The child environment remains fixed throughout this argument.
-/

namespace EditApproximation

open Finset



/-- The actual per-group failure test uses the rational estimated costs. -/
def unskippedGroupFailure {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P thetaExponent : ℕ) (tau F : ℚ)
    (child initial value : Fin M → TargetInterval target.length → ℚ) (Q : ℕ)
    (members : List (UnskippedBand source target parent b P thetaExponent tau F child initial))
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (gamma : ℚ) : Bool :=
  members.any fun member => decide (gamma * b <
    |dyadicUnskippedGroupEstimate Q value member draw -
      rationalEndpointActionValue member.center member.rounded value|)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RoundedGroupStates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Enumerating rounded endpoints with a length-gap guard costs only
one wide coordinate and one envelope coordinate. -/

namespace EditApproximation



theorem lengthGap_guard_distance {n : ℕ} (r : TargetInterval n) (sourceLength : ℕ) (h : ℚ)
    (hguard : |(r.hi : ℚ) - r.lo - sourceLength| ≤ 2 * h) :
    Nat.dist (r.lo + sourceLength) r.hi ≤ ⌈2 * h⌉₊ := by
  have hcast : (Nat.dist (r.lo + sourceLength) r.hi : ℚ) =
      |(r.hi : ℚ) - r.lo - sourceLength| := by
    have hd : |((r.lo + sourceLength : ℕ) : ℚ) - r.hi| =
        (Nat.dist (r.lo + sourceLength) r.hi : ℚ) := by
      exact_mod_cast natural_distance_cast (r.lo + sourceLength) r.hi
    rw [← hd, abs_sub_comm]
    congr 1
    push_cast
    ring
  have hbound : (Nat.dist (r.lo + sourceLength) r.hi : ℚ) ≤ (⌈2 * h⌉₊ : ℚ) :=
    hcast.le.trans (hguard.trans (Nat.le_ceil _))
  exact_mod_cast hbound

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ActualRoundedGroupInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Every actual unskipped rounded group input belongs to a common
small endpoint list determined by the cell, child and envelope label. -/

namespace EditApproximation



theorem groupRoundSpacing_pos (exponent : ℕ) (h : ℚ) : 0 < groupRoundSpacing exponent h := by
  apply Nat.ceil_pos.mpr
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem gridStateBox_sound {n g radius lo hi : ℕ} (hg : 0 < g) (r : TargetInterval n)
    (hr : r ∈ gridStateBox n g radius lo hi) :
    Nat.dist lo r.lo ≤ radius ∧ Nat.dist hi r.hi ≤ radius ∧ g ∣ r.lo ∧ g ∣ r.hi := by
  obtain ⟨s, hs, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨t, ht, hmake⟩ := List.mem_filterMap.mp hr
  have heq : r.lo = s ∧ r.hi = t := by
    unfold makeTargetState at hmake
    split_ifs at hmake with hvalid
    cases hmake
    exact ⟨rfl, rfl⟩
  rw [← heq.1] at hs
  rw [← heq.2] at ht
  have hlo := gridPointsBetween_sound hg hs
  have hhi := gridPointsBetween_sound hg ht
  refine ⟨?_, ?_, hlo.2.2, hhi.2.2⟩ <;> unfold Nat.dist <;> omega



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_CurrentQueryInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Distinct current-index inputs of the bounded query loops. The cover
includes all whole-cell shared estimates, selected cell actions, and
online actions; repeated uses do not add recursive calls. -/

namespace EditApproximation

open Finset

theorem actionCurrentInputCover_mem {Parent Child : Type*} [DecidableEq Child] {M : ℕ}
    (actions : List (RationalBellmanAction Parent Child M))
    (action : RationalBellmanAction Parent Child M) (ha : action ∈ actions) (i : Fin M) :
    action.childState i ∈ actionCurrentInputCover actions := by
  obtain ⟨index, hindex⟩ := List.mem_iff_get.mp ha
  apply Finset.mem_biUnion.mpr
  refine ⟨index, by simp, ?_⟩
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by rw [hindex]⟩

def currentQueryInputCover {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial current : Fin M → TargetInterval target.length → ℚ)
    (draw : CellGroupDraws M F Q) (q : TargetInterval target.length)
    (online : List (PhysicalRationalAction M target.length)) : Finset (Fin M × TargetInterval target.length) :=
  querySharedInputCover source target parent N F exponent Q a parentInitial q draw ∪
    actionCurrentInputCover (localCellGroupActions source target parent N P F exponent Q tau a parentInitial
      child initial current draw q) ∪ actionCurrentInputCover online

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GroupInputDependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shared group estimates depend only on the explicitly bounded sampled
input cover. Thus scanning or repeatedly scoring all cell members can
reuse gathered values rather than issue new recursive requests. -/

namespace EditApproximation

open Finset

theorem groupScaleEstimate_congr_queried {M Q b : ℕ} (h : ℚ)
    (envelope value value' : Fin M → ℚ)
    (draw : Fin (groupSampleCount M Q b h) → Fin M)
    (hvalue : ∀ i ∈ groupQueriedChildLabels M Q b h draw,
      envelope i = h → value i = value' i) :
    groupScaleEstimate (groupSampleCount M Q b h) h envelope value draw =
      groupScaleEstimate (groupSampleCount M Q b h) h envelope value' draw := by
  unfold groupScaleEstimate
  split_ifs with hexact
  · unfold groupScaleTrueCost
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hi
    · exact hvalue i (by simp only [groupQueriedChildLabels, hexact, ↓reduceIte, Finset.mem_univ]) hi
    · rfl
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hj
    · apply hvalue _ _ hj
      simp only [groupQueriedChildLabels, hexact, ↓reduceIte]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    · rfl

theorem rational_argmax_congr_on {ι : Type*} (members : List ι) (score score' : ι → ℚ)
    (hscore : ∀ member ∈ members, score member = score' member) :
    members.argmax score = members.argmax score' := by
  induction members with
  | nil => rfl
  | cons first rest ih =>
    rw [List.argmax_cons, List.argmax_cons, ih (fun member hm => hscore member (by simp [hm]))]
    cases hmax : rest.argmax score' with
    | none => rfl
    | some selected =>
      have hmem : selected ∈ rest := List.argmax_mem (by rw [hmax]; simp)
      dsimp only
      rw [hscore first (by simp), hscore selected (by simp [hmem])]

theorem selectGroupMember_congr_on {ι : Type*} (members : List ι) (hne : members ≠ [])
    (estimate estimate' : ι → ℚ)
    (heq : ∀ member ∈ members, estimate member = estimate' member) :
    selectGroupMember members hne estimate = selectGroupMember members hne estimate' := by
  unfold selectGroupMember
  rw [rational_argmax_congr_on members (fun member => -estimate member)
    (fun member => -estimate' member) (fun member hm => congrArg Neg.neg (heq member hm))]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySampledGroupPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed polynomial bounds the actual sampled-member bit counter. The
scale is supplied through its bit length, so a large distance scale does
not introduce a spurious linear dependence on that scale. -/

namespace EditApproximation

def sampledGroupEnvironment (M T exponent b vertices B : ℕ) : Fin 6 → ℕ
  | 0 => M
  | 1 => T
  | 2 => exponent
  | 3 => Nat.size b
  | 4 => vertices
  | _ => B

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryTriangularChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The optimizer's sampled iteration is obtained by the exact triangular
block search, with every threshold multiplication and comparison charged. -/

namespace EditApproximation



def triangularChoiceBitBudget (K B : ℕ) : ℕ :=
  (K + 1) * (10000 * (B + 3) ^ 2 + 30 * (B + 3))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandActionPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed-degree envelope for the full labeled action selector, including
its final logarithm-gradient and argmax, after the iterative optimizer. -/

namespace EditApproximation

def bandActionEnvironment (M d b v G K t Be Bk Bi Bt E : ℕ) : Fin 12 → ℕ
  | 0 => M
  | 1 => d
  | 2 => Nat.size b
  | 3 => v
  | 4 => G
  | 5 => K
  | 6 => t
  | 7 => Be
  | 8 => Bk
  | 9 => Bi
  | 10 => Bt
  | _ => E

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySampledOnlinePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete sampled online action, including the triangular search,
coordinate equality tests, final logarithm-gradient and labeled argmax. -/

namespace EditApproximation

def sampledOnlineOverheadEnv (M v d K B : ℕ) : Fin 5 → ℕ
  | 0 => M
  | 1 => v
  | 2 => d
  | 3 => K
  | _ => B

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The actual finite coarse randomness

At each internal node, the child thresholds are independent uniform labels.
Recursive subtrees are independent of these labels. This complete probability
space also includes labels below pruned nodes.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

universe u

instance coarseDrawsFintype (B D : ℕ) : Fintype (CoarseThresholdDraws B D) := by
  induction D with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ D ih =>
    letI := ih
    exact inferInstanceAs (Fintype ((Fin B → Fin B) × (Fin B → CoarseThresholdDraws B D)))

def coarseCanonicalDraws (B : ℕ) : (D : ℕ) → CoarseThresholdDraws B D
  | 0 => PUnit.unit
  | D + 1 => (id, fun _ => coarseCanonicalDraws B D)

instance coarseDrawsInhabited (B D : ℕ) : Inhabited (CoarseThresholdDraws B D) :=
  ⟨coarseCanonicalDraws B D⟩



instance coarseDrawsMeasurableSingletonClass (B D : ℕ)
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)] :
    MeasurableSingletonClass (CoarseThresholdDraws B D) := by
  induction D with
  | zero => exact inferInstanceAs (MeasurableSingletonClass PUnit)
  | succ D ih =>
    let := ih
    exact inferInstanceAs
      (MeasurableSingletonClass ((Fin B → Fin B) × (Fin B → CoarseThresholdDraws B D)))

/-- Literal recursive independent label law, with a deterministic leaf. -/


instance coarseDrawMeasure_isProbabilityMeasure (B D : ℕ) [NeZero B]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)] :
    IsProbabilityMeasure (coarseDrawMeasure B D) := by
  induction D with
  | zero =>
    change IsProbabilityMeasure (Measure.dirac (α := PUnit) PUnit.unit)
    exact Measure.dirac.isProbabilityMeasure
  | succ D ih =>
    let := ih
    change IsProbabilityMeasure
      ((Measure.pi fun _ : Fin B => (PMF.uniformOfFintype (Fin B)).toMeasure).prod
        (Measure.pi fun _ : Fin B => coarseDrawMeasure B D))
    exact Measure.prod.instIsProbabilityMeasure _ _

/-- Symbolic number of internal nodes in a complete coarse tree. -/
def coarseInternalNodes (B : ℕ) : ℕ → ℕ
  | 0 => 0
  | D + 1 => 1 + B * coarseInternalNodes B D

/-- Actual source starts of all children of a literal list traversal. -/
def coarseChildListStart {B D : ℕ} {α : Type u}
    (children : List (CoarseSourceTree B α D)) (start : ℕ) (i : Fin children.length) : ℕ :=
  start + ((children.take i.val).map CoarseSourceTree.word).flatten.length

/-- Source starts attached to the full child metadata list. -/
def coarseDataListStart {B D : ℕ} {α : Type u}
    (children : List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D))
    (start : ℕ) (i : Fin children.length) : ℕ :=
  start + ((children.take i.val).map (fun data => data.1.word)).flatten.length

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# The executable initial integer estimate

The direct branches handle long targets and equality. The remaining branch
evaluates the concrete coarse recurrence at every dyadic guess, takes the
rational minimum, rounds up and clamps to the input length.
-/

namespace EditApproximation

open EditDistortion Finset MeasureTheory ProbabilityTheory

universe u

/-- Independent finite coarse streams for the listed dyadic guesses. -/


instance coarseInitialMeasure_isProbabilityMeasure (B D n : ℕ) [NeZero B]
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)] :
    IsProbabilityMeasure (coarseInitialMeasure B D n) := by
  unfold coarseInitialMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseGlobalSeed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Simultaneous seed failure with the computed parameters

The count includes every dyadic guess, complete coarse-tree node and shift.
Independent finite entry streams realize the actual full table law.
Symbolic recursion indices carry exact equalities to the computed parameters.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

/-- Multiplicity of all local Bernstein tails for one complete entry. -/
def coarseEntryTailCount (B D n : ℕ) : ℕ :=
  (Nat.clog 2 n + 1) * coarseInternalNodes B D * (4 * (2 * 2 ^ Nat.clog 2 n + 1))





instance coarseFullSeedMeasure_isProbabilityMeasure (B : ℕ) [NeZero B]
    {I α : Type*} [Fintype I] (depth : I → ℕ) (x y : I → List α)
    [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)] :
    IsProbabilityMeasure (coarseFullSeedMeasure B depth x y) := by
  unfold coarseFullSeedMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RankedMemoProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Well-founded recursive memo evaluation. A local query program may
choose later requests from earlier answers. Each recursive request carries
its strict rank decrease; no complete table is evaluated in advance. -/

namespace EditApproximation





namespace FiniteQuery

def value {ι : Type*} (oracle : ι → ℚ) : FiniteQuery ι → ℚ
  | .done result => result
  | .read key next => value oracle (next (oracle key))



end FiniteQuery

def rankedProgramValue {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key}) (key : κ) : ℚ :=
  (program key).value (fun child => rankedProgramValue rank program child.val)
termination_by rank key
decreasing_by exact child.property



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RankedMemoWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counts of the actual persistent interpreter. Dictionary operations
are charged on every request, including hits; insertion and retained-node
costs are charged only when a value is computed. -/

namespace EditApproximation

namespace FiniteQuery

def cost {ι : Type*} (oracle : ι → ℚ) (weight : ι → ℕ) : FiniteQuery ι → ℕ
  | .done _ => 0
  | .read key next => weight key + cost oracle weight (next (oracle key))

def keys {ι : Type*} (oracle : ι → ℚ) : FiniteQuery ι → List ι
  | .done _ => []
  | .read key next => key :: keys oracle (next (oracle key))

end FiniteQuery

/-- Number of requests in the same adaptive program without cache hits.
It is a dominating execution tree, not the size of the full table. -/
def rankedUncachedCalls {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key}) (key : κ) : ℕ :=
  (program key).cost (fun child => rankedProgramValue rank program child.val)
    (fun child => rankedUncachedCalls rank program child.val) + 1
termination_by rank key
decreasing_by exact child.property

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Expected active work in the concrete pruned coarse tree

The counter records the array units of the actual execution; pruning stops
all descendant visits. Constant child overhead is charged to its expanded
parent. The linear-sweep proof converts these units to rational operations;
bit/RAM charging is separate.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

universe u



/- Array units actually incurred before pruning terminates a subtree. -/


/-- Finite conditional expectation recurrence for the same active work.
The root labels are independent uniforms, and each child uses its own
independent recursive label tree. -/
noncomputable def coarseExpectedArrayWork {B : ℕ} {α : Type u} (k : ℕ) (Q lam : ℚ) :
    {D : ℕ} → CoarseSourceTree B α D → ℚ → ℝ
  | _, tree, allowance =>
    if (tree.word.length : ℚ) ≤ allowance then 0 else
    match tree with
    | .leaf _ => (B * (2 * k + 1) : ℕ)
    | .branch children =>
      (B * (2 * k + 1) : ℕ) +
        ∑ i : Fin B, uniformMean (fun draw : Fin B =>
          coarseExpectedArrayWork k Q lam (children i)
            (lam * coarseChildThreshold B Q allowance draw))

noncomputable def coarseInverseAllowanceFactor (B : ℕ) (Q lam : ℚ) : ℝ :=
  (Q : ℝ) / lam * ∑ r ∈ Icc 1 B, (1 : ℝ) / r

noncomputable def coarseWorkMultiplier (factor : ℝ) (D : ℕ) : ℝ :=
  ∑ r ∈ range (D + 1), factor ^ r

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_AccuracyCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A computable fixed-accuracy cutoff. The algorithm tests the small-log
conditions directly; it does not construct the double exponential bound. -/

namespace EditApproximation





def accuracyCutoffExponent (epsilon : ℚ) : ℕ := max (2 ^ 1000) ⌈10 / epsilon⌉₊

def accuracyCutoff (epsilon : ℚ) : ℕ := 2 ^ (2 ^ accuracyCutoffExponent epsilon)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseWorkAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The depth-dependent scalar overhead of the actual initial estimator.
The expected array-counter bound includes every pruning outcome. -/

namespace EditApproximation

open Filter
open scoped Topology

def computedMaxCoarseDepth (N : ℕ) : ℕ := computedCoarseDepth N N

noncomputable def computedCoarseOverheadExponent (C : ℝ) (N : ℕ) : ℝ :=
  C * ((computedMaxCoarseDepth N : ℝ) + coarseExponent (inputSmallLog N) + 1) *
    Real.log (inputHeight N : ℝ)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedStageParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical premises for the computed physical refinement stage. -/

namespace EditApproximation

 theorem computed_stage_grid_bounds (N : ℕ) (hN : 0 < N) :
    66 ≤ (integerParameters N).P ∧
      (800 * (inputHeight N : ℝ) ^ 2) ≤ (integerParameters N).P ∧
      4 * ((integerParameters N).M : ℝ) / (integerParameters N).P ≤ 1 := by
  let H := inputHeight N
  let P := (integerParameters N).P
  let M := (integerParameters N).M
  have hHtwo : 2 ≤ H := by
    have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (heightExponent_pos N hN)
    simpa only [H, inputHeight, pow_one] using h
  have hHone : 1 ≤ H := by omega
  have hM : M ≤ H := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (Nat.div_le_self _ _)
  have hH18 : 800 ≤ H ^ 18 := by
    have h := Nat.pow_le_pow_left hHtwo 18
    norm_num only [show (2 : ℕ) ^ 18 = 262144 by norm_num] at h
    omega
  have hP20 : H ^ 20 ≤ P := pow_le_pow_right₀ hHone (by omega : 20 ≤ coarseExponent (inputSmallLog N) + 20)
  have hP800 : 800 * H ^ 2 ≤ P := by
    calc
      800 * H ^ 2 ≤ H ^ 18 * H ^ 2 := Nat.mul_le_mul_right _ hH18
      _ = H ^ 20 := by rw [← pow_add]
      _ ≤ P := hP20
  have hHP : (800 * (H : ℝ) ^ 2) ≤ P := by exact_mod_cast hP800
  have hP66 : 66 ≤ P := by
    have h : 4 ≤ H ^ 2 := by nlinarith only [hHtwo]
    nlinarith only [hP800, h]
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hHr : (2 : ℝ) ≤ H := by exact_mod_cast hHtwo
  have hMr : (M : ℝ) ≤ H := by exact_mod_cast hM
  refine ⟨hP66, hHP, ?_⟩
  apply (div_le_one₀ hPr).2
  nlinarith only [hHP, hHr, hMr]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterDependencyAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual pass/index count and the exponents in the dependency-path
bound. These statements concern computed numbers, independently of the
proof that an evaluator satisfies the dependency budgets. -/

namespace EditApproximation

open Filter
open scoped Topology

def computedDependencyIndexCount (N : ℕ) : ℕ :=
  (computedSeedPassCount N + 1) * ((integerParameters N).T + (integerParameters N).S + 1)

def computedMaxTreeDepth (N : ℕ) : ℕ := intervalTreeDepth (integerParameters N).M N

noncomputable def computedDependencyOverheadExponent (C₁ C₂ : ℝ) (N : ℕ) : ℝ :=
  (1 + Real.log 2) * ((computedMaxTreeDepth N : ℝ) + computedDependencyIndexCount N + 2) +
    C₁ * computedMaxTreeDepth N * Real.log (inputSmallLog N : ℝ) +
    C₂ * ((coarseExponent (inputSmallLog N) : ℝ) + 1) * computedDependencyIndexCount N *
      Real.log (inputHeight N : ℝ)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Work
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite dependency-path accounting

The double sum is the dependency-path budget in Section 10 of the
edit-distance manuscript, with separate branching bounds for same-index
and earlier-index requests.
-/

namespace EditApproximation

open Finset

/-- Overcount of dependency paths with at most `depth` descending edges
and `indices` strictly earlier-index/pass edges. -/
def dependencyPathBudget (depth indices same earlier : ℕ) : ℕ :=
  ∑ r ∈ range (depth + 1), ∑ s ∈ range (indices + 1),
    (r + s).choose r * same ^ r * earlier ^ s

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCoarseWidthCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual coarse array counter has a common source-width overhead.
Its exponent is sublinear in the computed logarithmic height. -/

namespace EditApproximation

open MeasureTheory

def computedCoarseWidthOverhead (N : ℕ) : ℕ :=
  6 * (integerParameters N).B * (Nat.clog 2 N + 1) * (computedMaxCoarseDepth N + 1) *
    inputHeight N ^ (8 * computedMaxCoarseDepth N)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseFirstRequestCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First-request work for a complete independent coarse source. The
query is adaptive; each entry is charged only on its first appearance.
No conditioning on seed correctness occurs in this estimate. -/

namespace EditApproximation

open MeasureTheory

section FirstRequest

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
  (N B : ℕ) [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
  (depth : ι → ℕ) (x y : ι → List α) (query : FiniteQuery ι)

noncomputable def coarseFirstRequestWork (draw : CoarseFullSeedDraws B depth x y) : ℝ :=
  ∑ i, selectionIndicator (i ∈ query.keys
    (fun j => (coarseFullSeedTable N B depth x y draw j : ℚ))) *
      (coarseInitialArrayWork B (depth i) (initialThresholdQ N) (initialLambda N) (x i) (y i) (draw i) : ℝ)

end FirstRequest

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseTransforms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Linear sweeps for the coarse penalty transform

The finite minima define the semantic arrays. These sweeps compute them
with one rational addition and one comparison per scan transition.
-/

namespace EditApproximation

open Finset

/-- The executable left sweep; Lean's `scanl` traverses its input once. -/
def coarseLeftSweep : List ℚ → List ℚ
  | [] => []
  | first :: rest => rest.scanl (fun previous value => min value (previous + 2)) first

/-- Literal array output of the two linear sweeps. -/
def coarsePenaltyTransform (source : List ℚ) : List ℚ :=
  List.zipWith min (coarseLeftSweep source) (coarseLeftSweep source.reverse).reverse

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Accuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Accuracy assembly for the edit-distance approximation scheme

The probability and integer-conversion bounds of Section 8 of
*An Almost-Linear Approximation Scheme for Edit Distance*
(OpenAI, September 24, 2026) follow from the refinement estimate and
simultaneous seed guarantee using Markov's inequality.
-/

namespace EditApproximation

open MeasureTheory

/-- The implementation clamps to the input length and rounds down. -/
noncomputable def integerAnswer (N : ℕ) (value : ℝ) : ℕ :=
  ⌊max 0 (min (N : ℝ) value)⌋₊

@[simp] theorem integerAnswer_zero (N : ℕ) : integerAnswer N 0 = 0 := by
  simp [integerAnswer, Nat.cast_nonneg]

/-- The positive excess on executions having a good seed. -/
noncomputable def goodExcess {Ω : Type*} (G : Set Ω) (value : Ω → ℝ) (D : ℕ) :
    Ω → ℝ := G.indicator (fun ω => max (value ω - D) 0)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PartitionIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Valid target states from an actual alignment partition

Prefix lengths convert an ordered list partition of a target substring
to valid global endpoint states. Every returned substring is exactly
the corresponding partition piece, even when pieces are empty.
-/

namespace EditApproximation

theorem flatten_take_length_le {α : Type*} (parts : List (List α)) (k : ℕ) :
    (parts.take k).flatten.length ≤ parts.flatten.length := by
  have h := congrArg (fun p : List (List α) => p.flatten.length)
    (List.take_append_drop k parts)
  simp only [List.flatten_append, List.length_append] at h
  omega

theorem flatten_take_succ_length {α : Type*} (parts : List (List α)) (i : Fin parts.length) :
    (parts.take (i.val + 1)).flatten.length =
      (parts.take i.val).flatten.length + parts[i.val].length := by
  rw [List.take_succ_eq_append_getElem i.isLt]
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.length_append]

theorem substring_middle {α : Type*} (pre piece suffix : List α) :
    substring ((pre ++ piece) ++ suffix) pre.length (pre.length + piece.length) = piece := by
  unfold substring
  rw [← List.length_append, List.take_append_length, List.drop_append_length]

theorem substring_flatten_piece {α : Type*} (parts : List (List α)) (i : Fin parts.length) :
    substring parts.flatten (parts.take i.val).flatten.length
      (parts.take (i.val + 1)).flatten.length = parts[i.val] := by
  have hparts : parts.flatten =
      ((parts.take i.val).flatten ++ parts[i.val]) ++ (parts.drop (i.val + 1)).flatten := by
    have h := congrArg List.flatten (List.take_append_drop (i.val + 1) parts)
    rw [List.take_succ_eq_append_getElem i.isLt] at h
    simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil,
      List.append_nil] using h.symm
  rw [flatten_take_succ_length]
  conv_lhs => arg 1; rw [hparts]
  exact substring_middle _ _ _

def partitionInterval {α : Type*} (target : List α) (q : TargetInterval target.length)
    (parts : List (List α)) (hparts : parts.flatten = substring target q.lo q.hi)
    (i : Fin parts.length) : TargetInterval target.length where
  lo := q.lo + (parts.take i.val).flatten.length
  hi := q.lo + (parts.take (i.val + 1)).flatten.length
  ordered := by rw [flatten_take_succ_length]; omega
  valid := by
    have hprefix := flatten_take_length_le parts (i.val + 1)
    have hlength := congrArg List.length hparts
    simp only [substring, List.length_drop, List.length_take, Nat.min_eq_left q.valid] at hlength
    have horder := q.ordered
    have hvalid := q.valid
    omega

theorem substring_inside_shift {α : Type*} (target : List α)
    (q : TargetInterval target.length) (lo hi : ℕ)
    (hhi : hi ≤ q.hi - q.lo) :
    substring target (q.lo + lo) (q.lo + hi) =
      substring (substring target q.lo q.hi) lo hi := by
  unfold substring
  rw [List.take_drop]
  have htake : q.lo + hi ≤ q.hi := by have h := q.ordered; omega
  simp only [List.take_take, Nat.min_eq_left htake, List.drop_drop]

theorem partitionInterval_substring {α : Type*} (target : List α)
    (q : TargetInterval target.length) (parts : List (List α))
    (hparts : parts.flatten = substring target q.lo q.hi) (i : Fin parts.length) :
    substring target (partitionInterval target q parts hparts i).lo
      (partitionInterval target q parts hparts i).hi = parts[i.val] := by
  have hhi : (parts.take (i.val + 1)).flatten.length ≤ q.hi - q.lo := by
    have h := flatten_take_length_le parts (i.val + 1)
    rw [hparts] at h
    simpa only [substring, List.length_drop, List.length_take, Nat.min_eq_left q.valid] using h
  change substring target (q.lo + (parts.take i.val).flatten.length)
    (q.lo + (parts.take (i.val + 1)).flatten.length) = parts[i.val]
  rw [substring_inside_shift target q _ _ hhi, ← hparts]
  exact substring_flatten_piece parts i

theorem partitionInterval_shared {α : Type*} (target : List α)
    (q : TargetInterval target.length) (parts : List (List α))
    (hparts : parts.flatten = substring target q.lo q.hi)
    (i j : Fin parts.length) (hnext : j.val = i.val + 1) :
    (partitionInterval target q parts hparts i).hi =
      (partitionInterval target q parts hparts j).lo := by
  simp only [partitionInterval, hnext]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_AlignedStates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual optimal child states

The alignment split is converted to bounded target endpoint states at
the actual balanced source children. Its sum is exactly the parent
edit distance; its target endpoints are shared.
-/

namespace EditApproximation

open EditDistortion Finset

theorem zipWith_sum_ofFn {α β γ : Type*} [AddCommMonoid γ]
    {M : ℕ} (f : α → β → γ) (x : Fin M → α) (y : Fin M → β) :
    (List.zipWith f (List.ofFn x) (List.ofFn y)).sum = ∑ i, f (x i) (y i) := by
  have hlist : List.zipWith f (List.ofFn x) (List.ofFn y) =
      List.ofFn (fun i => f (x i) (y i)) := by
    apply List.ext_getElem
    · simp only [List.length_zipWith, List.length_ofFn, min_self]
    · intro i hi hj
      simp only [List.getElem_zipWith, List.getElem_ofFn]
  rw [hlist, List.sum_ofFn]

theorem optimal_balanced_child_states {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (parent : TargetInterval source.length)
    (q : TargetInterval target.length) :
    ∃ states : Fin M → TargetInterval target.length,
      (∑ i, stateEditCost
        (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (states i)) =
          stateEditCost (substring source parent.lo parent.hi) target q ∧
      (states ⟨0, hM⟩).lo = q.lo ∧
      (states ⟨M - 1, by omega⟩).hi = q.hi ∧
      (∀ i j : Fin M, j.val = i.val + 1 → (states i).hi = (states j).lo) ∧
      ∀ i : Fin M,
        Nat.dist (q.lo + ((sourceChild parent i).lo - parent.lo)) (states i).lo ≤
          stateEditCost (substring source parent.lo parent.hi) target q ∧
        Nat.dist (q.lo + ((sourceChild parent i).hi - parent.lo)) (states i).hi ≤
          stateEditCost (substring source parent.lo parent.hi) target q := by
  let parts := List.ofFn fun i : Fin M =>
    substring source (sourceChild parent i).lo (sourceChild parent i).hi
  have hpartsLength : parts.length = M := List.length_ofFn
  have hnonempty : parts ≠ [] := by intro h; have hl := congrArg List.length h; simp [hpartsLength] at hl; omega
  obtain ⟨targets, hlen, hflat, hcost⟩ := edit_partition_split parts hnonempty
    (substring target q.lo q.hi)
  have htargetsLength : targets.length = M := hlen.trans hpartsLength
  let states : Fin M → TargetInterval target.length := fun i =>
    partitionInterval target q targets hflat ⟨i.val, by omega⟩
  have hsource : parts.flatten = substring source parent.lo parent.hi :=
    sourceChild_partition source hM parent
  refine ⟨states, ?_, ?_, ?_, ?_, ?_⟩
  · have htargets : List.ofFn (fun i : Fin M => targets[i.val]'(by omega)) = targets := by
      apply List.ext_getElem
      · simp only [List.length_ofFn, htargetsLength]
      · intro i hi hj
        simp only [List.getElem_ofFn]
    have hsum : (∑ i : Fin M, edit
        (substring source (sourceChild parent i).lo (sourceChild parent i).hi)
        (targets[i.val]'(by omega))) = edit parts.flatten (substring target q.lo q.hi) := by
      rw [← zipWith_sum_ofFn, htargets]
      exact hcost
    rw [hsource] at hsum
    convert hsum using 1
    · apply sum_congr rfl
      intro i hi
      change edit _ (substring target (partitionInterval target q targets hflat _).lo
        (partitionInterval target q targets hflat _).hi) = _
      rw [partitionInterval_substring]
    · rfl
  · simp only [states, partitionInterval, List.take_zero, List.flatten_nil,
      List.length_nil, Nat.add_zero]
  · have hlast : M - 1 + 1 = targets.length := by omega
    have hlength := congrArg List.length hflat
    simp only [substring, List.length_drop, List.length_take, Nat.min_eq_left q.valid] at hlength
    change q.lo + (targets.take (M - 1 + 1)).flatten.length = q.hi
    rw [hlast, List.take_length]
    have horder := q.ordered
    omega
  · intro i j hnext
    exact partitionInterval_shared target q targets hflat _ _ hnext
  · have hprefixBound (j : ℕ) :
        Nat.dist (q.lo + (parts.take j).flatten.length)
          (q.lo + (targets.take j).flatten.length) ≤
            stateEditCost (substring source parent.lo parent.hi) target q := by
      have h := optimal_partition_anchor_shift_bound parts targets
        (substring target q.lo q.hi) hlen.symm hcost j
      rw [natural_distance_cast] at h
      have hnat : Nat.dist (targets.take j).flatten.length (parts.take j).flatten.length ≤
          edit parts.flatten (substring target q.lo q.hi) := by exact_mod_cast h
      rw [hsource] at hnat
      change Nat.dist _ _ ≤ edit (substring source parent.lo parent.hi) (substring target q.lo q.hi)
      unfold Nat.dist at hnat ⊢
      omega
    intro i
    constructor
    · have h := hprefixBound i.val
      dsimp only [parts] at h
      rw [sourceChildren_prefix_length source hM parent i.val (by omega)] at h
      exact h
    · have h := hprefixBound (i.val + 1)
      dsimp only [parts] at h
      rw [sourceChildren_prefix_length source hM parent (i.val + 1) (by omega)] at h
      exact h

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_WideEarlierInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Wide enumeration gathers child states before scoring its Cartesian
action list. Its recursive input count depends on the coordinate lists,
rather than the exponentially larger number of complete actions. -/

namespace EditApproximation

open Finset

theorem wideEarlierInputCover_mem {nx ny M : ℕ} (parent : TargetInterval nx) (P history : ℕ)
    (representatives : List (ℕ × TargetInterval ny)) (b : ℕ) (r : TargetInterval ny)
    (hrep : (b, r) ∈ representatives) (t : ℕ) (ht : t < history)
    (action : Fin M → TargetInterval ny) (ha : action ∈ wideActionList M parent r b P)
    (i : Fin M) : (i, t, action i) ∈ wideEarlierInputCover parent P history representatives := by
  apply Finset.mem_biUnion.mpr
  refine ⟨(b, r), List.mem_toFinset.mpr hrep, Finset.mem_biUnion.mpr ?_⟩
  refine ⟨i, Finset.mem_univ _, Finset.mem_biUnion.mpr ?_⟩
  refine ⟨t, Finset.mem_range.mpr ht, Finset.mem_image.mpr ?_⟩
  exact ⟨action i, List.mem_toFinset.mpr (finiteAssignments_sound M _ action ha i), rfl⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandEarlierDependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The band construction and its literal guards use only the child
coordinates of the finite wide action list. The result types retain the
full tables as indices, so acceptance and returned centers are compared
after projecting away proof fields. -/

namespace EditApproximation

open Finset

theorem rationalWidePrefixCost_congr_child {nx ny M : ℕ}
    (parent : TargetInterval nx) (r : TargetInterval ny) (states : Fin M → TargetInterval ny)
    (left right : Fin M → TargetInterval ny → ℚ) (j : ℕ) (p : ℚ)
    (heq : ∀ i, left i (states i) = right i (states i)) :
    rationalWidePrefixCost parent r states left j p =
      rationalWidePrefixCost parent r states right j p := by
  unfold rationalWidePrefixCost
  congr 1
  apply sum_congr rfl
  intro i hi
  rw [heq i]

theorem rationalWidePrefixMinimum_congr_child {nx ny M : ℕ}
    (parent : TargetInterval nx) (r : TargetInterval ny)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (left right : Fin M → TargetInterval ny → ℚ) (j : ℕ) (p : ℚ)
    (heq : ∀ action ∈ actions, ∀ i, left i (action i) = right i (action i)) :
    rationalWidePrefixMinimum parent r actions hne left j p =
      rationalWidePrefixMinimum parent r actions hne right j p := by
  have hcost (action) (ha : action ∈ actions) :=
    rationalWidePrefixCost_congr_child parent r action left right j p (heq action ha)
  unfold rationalWidePrefixMinimum
  rw [hcost _ (List.head_mem hne)]
  congr 1
  exact List.map_congr_left hcost

theorem rationalWideActionMinimum_congr_child {nx ny M : ℕ}
    (parent : TargetInterval nx) (r : TargetInterval ny) (b P : ℕ)
    (hne : wideActionList M parent r b P ≠ [])
    (left right : Fin M → TargetInterval ny → ℚ)
    (heq : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, left i (action i) = right i (action i)) :
    rationalWideActionMinimum parent r b P hne left =
      rationalWideActionMinimum parent r b P hne right := by
  have hcost (action) (ha : action ∈ wideActionList M parent r b P) :
      rationalEndpointActionValue r action left = rationalEndpointActionValue r action right := by
    unfold rationalEndpointActionValue
    congr 1
    exact sum_congr rfl (fun i hi => heq action ha i)
  unfold rationalWideActionMinimum
  rw [hcost _ (List.head_mem hne)]
  congr 1
  exact List.map_congr_left hcost

theorem computedBandActions_congr_child {nx ny M : ℕ}
    (parent : TargetInterval nx) (r : TargetInterval ny) (b P : ℕ) (tau theta velocity : ℚ)
    (left right : Fin M → TargetInterval ny → ℚ)
    (heq : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, left i (action i) = right i (action i)) :
    computedBandActions parent r b P tau theta velocity left =
      computedBandActions parent r b P tau theta velocity right := by
  unfold computedBandActions
  dsimp only
  split_ifs with hnonempty hvelocity
  · rfl
  · have hprefix (j : ℕ) (p : ℚ) := rationalWidePrefixMinimum_congr_child parent r
      (wideActionList M parent r b P) hnonempty left right j p heq
    simp only [bandActionPredicate, hprefix]
  · rfl

theorem bandChildEnvelope_congr_initial {ny M : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval ny)) (left right : Fin M → TargetInterval ny → ℚ)
    (heq : ∀ action ∈ band, ∀ i, left i (action i) = right i (action i)) :
    bandChildEnvelope b band left = bandChildEnvelope b band right := by
  funext i
  have hmap : band.map (fun action => left i (action i)) =
      band.map (fun action => right i (action i)) :=
    List.map_congr_left (fun action ha => heq action ha i)
  simp only [bandChildEnvelope, hmap]

theorem bandRoundSpacing_congr_initial {ny M : ℕ} (exponent b : ℕ)
    (band : List (Fin M → TargetInterval ny)) (left right : Fin M → TargetInterval ny → ℚ)
    (heq : ∀ action ∈ band, ∀ i, left i (action i) = right i (action i)) :
    bandRoundSpacing exponent b band left = bandRoundSpacing exponent b band right := by
  funext i
  have hmap : band.map (fun action => left i (action i)) =
      band.map (fun action => right i (action i)) :=
    List.map_congr_left (fun action ha => heq action ha i)
  simp only [bandRoundSpacing, bandEnvelopeExponent, hmap]

theorem canonicalRoundedBandAction_congr_initial {ny M : ℕ} (exponent b : ℕ)
    (band : List (Fin M → TargetInterval ny)) (hne : band ≠ [])
    (left right : Fin M → TargetInterval ny → ℚ)
    (heq : ∀ action ∈ band, ∀ i, left i (action i) = right i (action i)) :
    canonicalRoundedBandAction exponent b band hne left =
      canonicalRoundedBandAction exponent b band hne right := by
  unfold canonicalRoundedBandAction roundedBandAction
  rw [bandRoundSpacing_congr_initial exponent b band left right heq]

theorem testUnskippedBand_isSome_iff {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent : ℕ) (tau F : ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ) (r : TargetInterval target.length) :
    (testUnskippedBand source target parent b P exponent tau F child initial r).isSome = true ↔
      ∃ hne : representativeBandActions source target parent r b P tau
          ((2 : ℚ) ^ (-(exponent : ℤ))) child ≠ [],
        (∑ i, bandChildEnvelope b (representativeBandActions source target parent r b P tau
          ((2 : ℚ) ^ (-(exponent : ℤ))) child) initial i) ≤ 64 * F * b ∧
        canonicalRoundedBandAction exponent b (representativeBandActions source target parent r b P tau
          ((2 : ℚ) ^ (-(exponent : ℤ))) child) hne initial ∈ wideActionList M parent r b P ∧
        ∀ i, |rationalStateGap
          (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target
          (canonicalRoundedBandAction exponent b (representativeBandActions source target parent r b P tau
            ((2 : ℚ) ^ (-(exponent : ℤ))) child) hne initial i)| ≤
              2 * bandChildEnvelope b (representativeBandActions source target parent r b P tau
                ((2 : ℚ) ^ (-(exponent : ℤ))) child) initial i := by
  unfold testUnskippedBand
  dsimp only
  split_ifs with hband hsum hwide hgap
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨hne, _⟩
    exact hne hband
  · constructor
    · intro _
      exact ⟨hband, hsum, hwide, hgap⟩
    · intro _
      rfl
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨hne, _, _, hg⟩
    exact hgap hg
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨hne, _, hw, _⟩
    exact hwide hw
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨hne, hs, _⟩
    exact hsum hs

theorem testUnskippedBand_center_projection {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P exponent : ℕ) (tau F : ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ) :
    (testUnskippedBand source target parent b P exponent tau F child initial r).map
      UnskippedBand.center =
      if (testUnskippedBand source target parent b P exponent tau F child initial r).isSome
      then some r else none := by
  unfold testUnskippedBand
  dsimp only
  split_ifs <;> simp_all

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_DependencyExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite dependency expansions with two edge sorts. The certificate
checks progress and local branching at every actual node; the global
count follows from these local conditions. -/

namespace EditApproximation

open Finset

def dependencyWordCount (same earlier r s : ℕ) : ℕ :=
  (r + s).choose r * same ^ r * earlier ^ s

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GatheredLocalStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The current-index part of a local step can be evaluated in two
stages: gather the shared sampled inputs, select the whole-cell actions,
then gather their actual costs and the online action costs. -/

namespace EditApproximation

open Finset

theorem rationalActionValues_congr_cover {Parent Child : Type*} [DecidableEq Child] {M : ℕ}
    (distance : Parent → Parent → ℚ) (L : ℚ)
    (actions : List (RationalBellmanAction Parent Child M)) (q : Parent)
    (value value' : Child → ℚ)
    (hvalue : ∀ input ∈ actionCurrentInputCover actions, value input = value' input) :
    actions.map (rationalActionValue distance L value q) =
      actions.map (rationalActionValue distance L value' q) := by
  apply List.map_congr_left
  intro action ha
  unfold rationalActionValue
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact hvalue _ (actionCurrentInputCover_mem actions action ha i)



theorem mem_orderedInputs {ι : Type*} [DecidableEq ι] (encode : ι → ℕ)
    (hinjective : Function.Injective encode) (inputs : Finset ι) (input : ι) :
    input ∈ orderedInputs encode hinjective inputs ↔ input ∈ inputs := by
  let _ : LinearOrder ι := LinearOrder.lift' encode hinjective
  exact Finset.mem_sort (r := (· ≤ ·))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalInputEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Fixed-width binary keys for gathered child states. The encoding uses
mixed radix arithmetic on the child label and the two state endpoints. -/

namespace EditApproximation

theorem mixedRadix_injective {radix lo lo' hi hi' : ℕ}
    (hlo : lo < radix) (hlo' : lo' < radix)
    (heq : lo + radix * hi = lo' + radix * hi') : lo = lo' ∧ hi = hi' := by
  have hmod := congrArg (fun n => n % radix) heq
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hlo'] at hmod
  refine ⟨hmod, ?_⟩
  apply Nat.mul_left_cancel (by omega : 0 < radix)
  omega



theorem childInputCode_injective (M n : ℕ) :
    Function.Injective (@childInputCode M n) := by
  rintro ⟨i, q⟩ ⟨i', q'⟩ heq
  obtain ⟨hi, hq⟩ := mixedRadix_injective i.isLt i'.isLt heq
  have hqlo : q.lo < n + 1 := by have := q.ordered.trans q.valid; omega
  have hqlo' : q'.lo < n + 1 := by have := q'.ordered.trans q'.valid; omega
  obtain ⟨hlo, hhi⟩ := mixedRadix_injective hqlo hqlo' hq
  have hqeq : q = q' := by cases q; cases q'; cases hlo; cases hhi; rfl
  exact Prod.ext (Fin.ext hi) hqeq

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalWarmupQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Adaptive finite queries for the literal local initial cones and
warmup. Candidate lists are bounded local grid lists; no full target
domain is tabulated. -/

namespace EditApproximation

namespace FiniteQuery



theorem bind_value {ι : Type*} (oracle : ι → ℚ) (program : FiniteQuery ι)
    (next : ℚ → FiniteQuery ι) :
    (bind program next).value oracle = (next (program.value oracle)).value oracle := by
  induction program with
  | done result => rfl
  | read key continuation ih => exact ih (oracle key)



theorem collect_value {ι κ : Type*} (oracle : ι → ℚ) (reader : κ → FiniteQuery ι)
    (keys : List κ) (next : List ℚ → FiniteQuery ι) :
    (collect reader keys next).value oracle =
      (next (keys.map fun key => (reader key).value oracle)).value oracle := by
  induction keys generalizing next with
  | nil => rfl
  | cons key keys ih =>
    rw [collect, bind_value, ih]
    rfl

end FiniteQuery



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteQueryWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact read costs for the finite query combinators used in warmup
and refinement. In particular, a collected value is computed once and
is reused by the continuation's local arithmetic. -/

namespace EditApproximation.FiniteQuery

theorem keys_bind {ι : Type*} (oracle : ι → ℚ)
    (program : FiniteQuery ι) (next : ℚ → FiniteQuery ι) :
    (bind program next).keys oracle = program.keys oracle ++
      (next (program.value oracle)).keys oracle := by
  induction program with
  | done result => rfl
  | read key continuation ih =>
    simpa only [bind, keys, value, List.cons_append] using
      congrArg (List.cons key) (ih (oracle key))

theorem keys_collect {ι κ : Type*} (oracle : ι → ℚ)
    (reader : κ → FiniteQuery ι) (inputs : List κ) (next : List ℚ → FiniteQuery ι) :
    (collect reader inputs next).keys oracle =
      inputs.flatMap (fun input => (reader input).keys oracle) ++
      (next (inputs.map fun input => (reader input).value oracle)).keys oracle := by
  induction inputs generalizing next with
  | nil => rfl
  | cons input inputs ih =>
    simp only [collect, keys_bind, ih, List.flatMap_cons, List.map_cons, List.append_assoc]

theorem keys_all_collect {ι κ : Type*} (oracle : ι → ℚ) (predicate : ι → Prop)
    (reader : κ → FiniteQuery ι) (inputs : List κ) (next : List ℚ → FiniteQuery ι)
    (hreader : ∀ input ∈ inputs, ∀ key ∈ (reader input).keys oracle, predicate key)
    (hnext : ∀ values key, key ∈ (next values).keys oracle → predicate key) :
    ∀ key ∈ (collect reader inputs next).keys oracle, predicate key := by
  rw [keys_collect]
  intro key hkey
  rcases List.mem_append.mp hkey with hreaderKey | hnextKey
  · obtain ⟨input, hi, hk⟩ := List.mem_flatMap.mp hreaderKey
    exact hreader input hi key hk
  · exact hnext _ key hnextKey

end EditApproximation.FiniteQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RefinementErrorTerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit estimates for the actual four parts of the refinement error. -/

namespace EditApproximation

noncomputable def computedRefinementError (N nx : ℕ) : ℝ :=
  let ell : ℝ := inputSmallLog N
  let H : ℝ := inputHeight N
  let M : ℝ := (integerParameters N).M
  let J : ℝ := intervalTreeDepth (integerParameters N).M nx
  let P : ℝ := (integerParameters N).P
  let T : ℝ := (integerParameters N).T
  let S : ℝ := (integerParameters N).S
  let root := heightQuarterRoot N
  let q : ℝ := coarseExponent (inputSmallLog N) + 21
  (8 * M + 512 * ell) * J / P +
    (40000 * root * ell ^ 2 * (1 + J / P + J / T) +
      2 * J * (1 / root + 4 * (1 / ell ^ 4) * ell +
        (64 * ell * (4 * q * ell / ell ^ 5 + 2 * (1 / ell ^ 4) + S / H ^ 3) +
          2 * (1 / ell ^ 10) + 2 * S * (1 / H ^ 4) * ell))) / S

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ComparisonTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The input-determined rounded comparison tree

The choices here are only for the proof. They use the exact input edit
costs and a fixed classical choice of optimal alignment, and have no
sampling argument. Stopped states are carried in child zero, with the
remaining physical slots empty.
-/

namespace EditApproximation

open Finset

def comparisonStopped {α : Type*} (source target : List α)
    (parent : TargetInterval source.length) (q : TargetInterval target.length) : Prop :=
  parent.hi - parent.lo ≤ 1 ∨ stateEditCost (substring source parent.lo parent.hi) target q = 0

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalProgramNodeRegret
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual local and global expected regret of the complete finite selection program. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

noncomputable def physicalProgramNodeCoefficient (N F : ℕ) (η κ delta : ℚ) (S H : ℕ) : ℝ :=
  64 * (F : ℝ) *
    ((4 * (coarseExponent (inputSmallLog N) + 21 : ℕ) * (inputSmallLog N : ℝ)) / (η : ℝ) +
      2 * (κ : ℝ) + (S : ℝ) / (H : ℝ) ^ 3) +
    2 * (delta : ℝ) + 2 * S * (1 / (H : ℝ) ^ 4) * F

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalProgramComparisonRegret
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual selection program supplies the good-node premise of the
comparison-tree expected-regret telescope. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem computed_program_grid_lower (N P : ℕ) (hN : 0 < N)
    (hPeq : P = (integerParameters N).P) : 66 ≤ P := by
  rw [hPeq]
  exact (computed_stage_grid_bounds N hN).1

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RankedMemoSimulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local recurrence equalities identify the complete table semantics
of a lazy query program. No complete table is evaluated by the memo
interpreter; it is used only as the mathematical specification. -/

namespace EditApproximation

theorem rankedProgramValue_eq {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (expected : κ → ℚ)
    (hstep : ∀ key, (program key).value (fun child => expected child.val) = expected key)
    (key : κ) : rankedProgramValue rank program key = expected key := by
  have hall : ∀ level key, rank key = level → rankedProgramValue rank program key = expected key := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel
      rw [rankedProgramValue]
      have hchildren : (fun child : {child : κ // rank child < rank key} =>
          rankedProgramValue rank program child.val) = fun child => expected child.val := by
        funext child
        exact ih (rank child.val) (hlevel ▸ child.property) child.val rfl
      rw [hchildren]
      exact hstep key
  exact hall (rank key) key rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteQueryRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Restriction of adaptive read programs to a proved finite request domain.
The restriction visits the same reads whenever the original execution stays
in that domain. It does not enumerate the domain. -/

namespace EditApproximation.FiniteQuery



 theorem mapKeys_value {ι κ : Type*} (f : ι → κ) (oracle : κ → ℚ) (program : FiniteQuery ι) :
    (mapKeys f program).value oracle = program.value (oracle ∘ f) := by
  induction program with
  | done result => rfl
  | read key next ih => exact ih (oracle (f key))

 theorem mapKeys_keys {ι κ : Type*} (f : ι → κ) (oracle : κ → ℚ) (program : FiniteQuery ι) :
    (mapKeys f program).keys oracle = (program.keys (oracle ∘ f)).map f := by
  induction program with
  | done result => rfl
  | read key next ih => exact congrArg (List.cons (f key)) (ih (oracle (f key)))



end EditApproximation.FiniteQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RankedProgramRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restrict a well-founded query program to its proved finite key domain.
Values, executed read lists and weighted read costs are preserved. -/

namespace EditApproximation

 def restrictRankedProgram {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (P : κ → Prop) [DecidablePred P] (key : {key // P key}) :
    FiniteQuery {child : {key // P key} // rank child.val < rank key.val} :=
  FiniteQuery.mapKeys (fun child => ⟨⟨child.val.val, child.property⟩, child.val.property⟩)
    (FiniteQuery.restrict (fun child => P child.val) (program key.val))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalOnlineProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Direct online queries use one rounded center per allowed scale. The
integer argument denotes the accepted output of the exact rejection sampler;
reduction modulo the requested range merely makes the finite rule total. -/

namespace EditApproximation

open Finset



theorem keyedOnlineBandG_positive {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P exponent H b : ℕ) (tau : ℚ)
    (child : Fin M → TargetInterval target.length → ℚ) (r : TargetInterval target.length) :
    0 < keyedOnlineBandG source target parent P exponent H b tau child r := by
  unfold keyedOnlineBandG
  omega



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryEarlierInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! All wide-coordinate requests needed for one local query can be gathered
from bounded representative lists, including complete requested cells and
the rounded online center at every applicable scale. -/

namespace EditApproximation

open Finset



theorem queryEarlierRepresentatives_local {n : ℕ} (N P F exponent : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) (q : TargetInterval n) (br : ℕ × TargetInterval n)
    (hbr : br ∈ localRefinementRepresentatives N P F a initial q) :
    br ∈ queryEarlierRepresentatives N P F exponent a initial q := by
  exact List.mem_append_left _ (List.mem_append_left _ hbr)

theorem queryEarlierRepresentatives_cell {n : ℕ} (N P F exponent : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) (q : TargetInterval n) (key : ℕ × (ℕ × ℕ))
    (hkey : key ∈ localGroupQueryKeys N F exponent a initial q) (r : TargetInterval n)
    (hr : r ∈ cellRepresentativeStates n P F key.1 a initial ((2 : ℚ) ^ (-(exponent : ℤ))) key.2) :
    (key.1, r) ∈ queryEarlierRepresentatives N P F exponent a initial q := by
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨key, hkey, List.mem_map.mpr ⟨r, hr, rfl⟩⟩

theorem queryEarlierRepresentatives_online {n : ℕ} (N P F exponent : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) (q : TargetInterval n) (b : ℕ)
    (hb : b ∈ dyadicQueryWindow N (initial q) a F) :
    (b, roundInterval (seedGridSpacing b P) q) ∈
      queryEarlierRepresentatives N P F exponent a initial q := by
  exact List.mem_append_right _ (List.mem_map.mpr ⟨b, hb, rfl⟩)



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_EarlierValueDependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Wide Bellman scoring reads only the earlier child coordinates in the
explicit finite cover. Enumeration can reuse their gathered values. -/

namespace EditApproximation

open Finset

theorem wideActionValues_congr_earlier {nx ny M : ℕ}
    (parent : TargetInterval nx) (P history time : ℕ)
    (small large : List (ℕ × TargetInterval ny)) (hsub : ∀ br ∈ small, br ∈ large)
    (left right : Fin M → ℕ → TargetInterval ny → ℚ) (htime : time < history)
    (hvalues : ∀ input ∈ wideEarlierInputCover parent P history large,
      left input.1 input.2.1 input.2.2 = right input.1 input.2.1 input.2.2)
    (distance : TargetInterval ny → TargetInterval ny → ℚ) (L : ℚ) (q : TargetInterval ny) :
    (rationalActualWideActions parent small P).map
      (rationalActionValue distance L (fun input => left input.1 time input.2) q) =
    (rationalActualWideActions parent small P).map
      (rationalActionValue distance L (fun input => right input.1 time input.2) q) := by
  apply List.map_congr_left
  intro action ha
  obtain ⟨br, hbr, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨states, hs, rfl⟩ := List.mem_map.mp ha
  unfold rationalActionValue
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact hvalues (i, time, states i)
    (wideEarlierInputCover_mem parent P history large br.1 br.2
      (hsub br hbr) time htime states hs i)

theorem localBellman_congr_earlier {nx ny M : ℕ}
    (parent : TargetInterval nx) (N P F exponent history time : ℕ) (a : ℚ)
    (initial : TargetInterval ny → ℚ) (q : TargetInterval ny)
    (left right : Fin M → ℕ → TargetInterval ny → ℚ) (htime : time < history)
    (hvalues : ∀ input ∈ queryEarlierInputCover parent N P F exponent history a initial q,
      left input.1 input.2.1 input.2.2 = right input.1 input.2.1 input.2.2) (L : ℚ) :
    rationalBellman initial (fun q r => targetEndpointDistance q r) L
      (rationalActualWideActions parent (localRefinementRepresentatives N P F a initial q) P)
      (fun input => left input.1 time input.2) q =
    rationalBellman initial (fun q r => targetEndpointDistance q r) L
      (rationalActualWideActions parent (localRefinementRepresentatives N P F a initial q) P)
      (fun input => right input.1 time input.2) q := by
  unfold rationalBellman
  rw [wideActionValues_congr_earlier parent P history time _ _
    (queryEarlierRepresentatives_local N P F exponent a initial q)
    left right htime hvalues]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_OnlineEarlierDependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual online optimizer reads only the recorded band coordinates
and earlier child histories. Equality on the finite query cover suffices
for equality of its returned action, including deterministic tie breaking. -/

namespace EditApproximation

open Finset

theorem rationalLinearizationMaximizer_congr_on {ι : Type*}
    (coordinates : Finset ι) (vertices : List (ι → ℚ)) (left right : ι → ℚ)
    (heq : ∀ i ∈ coordinates, left i = right i) :
    rationalLinearizationMaximizer coordinates vertices left =
      rationalLinearizationMaximizer coordinates vertices right := by
  have hscore : (fun p : ι → ℚ => ∑ i ∈ coordinates, left i * p i) =
      (fun p : ι → ℚ => ∑ i ∈ coordinates, right i * p i) := by
    funext p
    exact sum_congr rfl (fun i hi => by rw [heq i hi])
  unfold rationalLinearizationMaximizer
  rw [hscore]

theorem finiteRationalOptimizer_congr_linear_on {ι : Type*}
    (coordinates : Finset ι) (vertices : List (ι → ℚ)) (left right : ι → ℚ)
    (G j : ℕ) (heq : ∀ i ∈ coordinates, left i = right i) :
    finiteRationalOptimizer coordinates vertices left G j =
      finiteRationalOptimizer coordinates vertices right G j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [finiteRationalOptimizer, ih]
    have hselected := rationalLinearizationMaximizer_congr_on coordinates vertices
      (rationalSmoothedGradient G left (finiteRationalOptimizer coordinates vertices right G j))
      (rationalSmoothedGradient G right (finiteRationalOptimizer coordinates vertices right G j))
      (fun i hi => by simp only [rationalSmoothedGradient, heq i hi])
    rw [hselected]

theorem finiteOptimizerAction_congr_linear_on {β σ : Type*}
    [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : List (β → σ)) (hband : band ≠ []) (mass : β → ℚ)
    (left right : β × σ → ℚ) (G j : ℕ)
    (heq : ∀ i ∈ bandCoordinates band.toFinset, left i = right i) :
    finiteOptimizerAction band hband mass left G j =
      finiteOptimizerAction band hband mass right G j := by
  unfold finiteOptimizerAction
  dsimp only
  rw [finiteRationalOptimizer_congr_linear_on _ _ left right G j heq]
  have hscore : (fun action : β → σ => ∑ i ∈ bandCoordinates band.toFinset,
      rationalSmoothedGradient G left
        (finiteRationalOptimizer (bandCoordinates band.toFinset) (band.map (actionVector mass)) right G j) i *
          actionVector mass action i) =
      (fun action : β → σ => ∑ i ∈ bandCoordinates band.toFinset,
      rationalSmoothedGradient G right
        (finiteRationalOptimizer (bandCoordinates band.toFinset) (band.map (actionVector mass)) right G j) i *
          actionVector mass action i) := by
    funext action
    apply sum_congr rfl
    intro i hi
    simp only [rationalSmoothedGradient, heq i hi]
  rw [hscore]

theorem finiteOptimizerActionDraw_congr_linear_on {β σ : Type*}
    [Fintype β] [DecidableEq β] [DecidableEq σ]
    (band : List (β → σ)) (hband : band ≠ []) (mass : β → ℚ)
    (left right : β × σ → ℚ) (G K : ℕ) (integer : Fin (optimizerTriangularMass K))
    (heq : ∀ i ∈ bandCoordinates band.toFinset, left i = right i) :
    finiteOptimizerActionDraw band hband mass left G K integer =
      finiteOptimizerActionDraw band hband mass right G K integer :=
  finiteOptimizerAction_congr_linear_on band hband mass left right G _ heq

/-- The gain at `t` and decrements at indices below `t` inspect exactly
the input table indices at most `t`. -/
theorem rationalOnlineLinear_child_congr {β σ : Type*} (mass : β → ℚ)
    (left right : ℕ → β × σ → ℚ) (eta kappa : ℚ) (t : ℕ) (i : β × σ)
    (heq : ∀ s ≤ t, left s i = right s i) :
    rationalOnlineLinear eta kappa (childGain mass left) (childDecrement mass left) t i =
      rationalOnlineLinear eta kappa (childGain mass right) (childDecrement mass right) t i := by
  have hgain (s : ℕ) (hs : s ≤ t) : childGain mass left s i = childGain mass right s i := by
    simp only [childGain, heq s hs]
  have hdecrement (s : ℕ) (hs : s < t) :
      childDecrement mass left s i = childDecrement mass right s i := by
    simp only [childDecrement, heq s (by omega), heq (s + 1) (by omega)]
  unfold rationalOnlineLinear rationalOptimisticHistory
  rw [hgain t le_rfl]
  congr 2
  apply sum_congr rfl
  intro s hs
  rw [hgain s (by have ht := mem_range.mp hs; omega), hdecrement s (mem_range.mp hs)]

theorem keyedOnlineCandidate_congr_history {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b : ℕ) (tau eta kappa : ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (left right : PhysicalChildTables M target.length) (t : ℕ)
    (r : TargetInterval target.length) (integer : ℕ)
    (heq : ∀ i ∈ bandCoordinates (representativeBandActions source target parent r b P tau
      ((2 : ℚ) ^ (-(exponent : ℤ))) child).toFinset, ∀ s ≤ t,
        left i.1 s i.2 = right i.1 s i.2) :
    keyedOnlineCandidate source target parent P F exponent H b tau eta kappa child initial left t r integer =
      keyedOnlineCandidate source target parent P F exponent H b tau eta kappa child initial right t r integer := by
  have hlinear : ∀ i ∈ bandCoordinates (representativeBandActions source target parent r b P tau
      ((2 : ℚ) ^ (-(exponent : ℤ))) child).toFinset,
      rationalOnlineLinear eta kappa
        (childGain (bandChildEnvelope b (representativeBandActions source target parent r b P tau
          ((2 : ℚ) ^ (-(exponent : ℤ))) child) initial) (fun s i => left i.1 s i.2))
        (childDecrement (bandChildEnvelope b (representativeBandActions source target parent r b P tau
          ((2 : ℚ) ^ (-(exponent : ℤ))) child) initial) (fun s i => left i.1 s i.2)) t i =
      rationalOnlineLinear eta kappa
        (childGain (bandChildEnvelope b (representativeBandActions source target parent r b P tau
          ((2 : ℚ) ^ (-(exponent : ℤ))) child) initial) (fun s i => right i.1 s i.2))
        (childDecrement (bandChildEnvelope b (representativeBandActions source target parent r b P tau
          ((2 : ℚ) ^ (-(exponent : ℤ))) child) initial) (fun s i => right i.1 s i.2)) t i := by
    intro i hi
    exact rationalOnlineLinear_child_congr _ _ _ eta kappa t i (heq i hi)
  unfold keyedOnlineCandidate
  dsimp only
  split_ifs with hband
  · rfl
  · cases htest : testUnskippedBand source target parent b P exponent tau F child initial r with
    | none => rfl
    | some data =>
      apply congrArg (fun action => some (sharedBandRationalAction r action))
      exact finiteOptimizerActionDraw_congr_linear_on _ hband _ _ _ _ _ _ hlinear

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RefinementBandSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Band-table congruence uses proof-free data. Equality of these data
preserves the ordered minimization and its tie decisions, even though the
guard records have different table-indexed types. -/

namespace EditApproximation

theorem rational_argmax_map {ι κ : Type*} (members : List ι) (project : ι → κ)
    (score : κ → ℚ) :
    (members.argmax (fun member => score (project member))).map project =
      (members.map project).argmax score := by
  induction members with
  | nil => rfl
  | cons first rest ih =>
    rw [List.map_cons, List.argmax_cons, List.argmax_cons, ← ih]
    cases hmax : rest.argmax (fun member => score (project member)) with
    | none => rfl
    | some selected =>
      dsimp only [Option.map]
      split_ifs <;> rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedCoarseOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All initial-entry information used by a charged table body arrives
through explicit requests. Flattening those requests gives an adaptive
coarse oracle program whose shape is independent of coarse answers. -/

namespace EditApproximation

namespace FiniteQuery

def substitute {ι κ : Type*} (ask : ι → FiniteQuery κ) : FiniteQuery ι → FiniteQuery κ
  | .done value => .done value
  | .read key next => bind (ask key) (fun value => substitute ask (next value))

end FiniteQuery

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedIndexCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The charged request index distinguishes previous passes and coarse
leaves. For internal refinement its two index classes are exactly the
current and earlier table-read counters. -/

namespace EditApproximation

def chargedSameWeight {M J ny passes copies T S : ℕ}
    (parent child : ChargedPhysicalRequest M J ny passes copies T S) : ℕ :=
  if ¬ child.index < parent.index then 1 else 0

def chargedEarlierWeight {M J ny passes copies T S : ℕ}
    (parent child : ChargedPhysicalRequest M J ny passes copies T S) : ℕ :=
  if child.index < parent.index then 1 else 0

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_AdaptiveSeedLaw
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fresh streams indexed by every possible incoming seed make adaptive
seed-dependent draw types compatible with a single finite product law. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Step

variable {Seed : Type*} [Fintype Seed] [DecidableEq Seed]
  [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  {Draw : Seed → Type*} [∀ seed, Fintype (Draw seed)]
  [∀ seed, MeasurableSpace (Draw seed)] [∀ seed, MeasurableSingletonClass (Draw seed)]
  (drawLaw : ∀ seed, Measure (Draw seed)) [∀ seed, IsProbabilityMeasure (drawLaw seed)]

/-- Only the coordinate belonging to the actual incoming table is consumed.
All states within that coordinate retain their shared copy streams. -/
def adaptiveSeedStep (next : ∀ seed, Draw seed → Seed) (pair : Seed × (∀ seed, Draw seed)) : Seed :=
  next pair.1 (pair.2 pair.1)

noncomputable def adaptiveSeedLaw (incoming : Measure Seed) (next : ∀ seed, Draw seed → Seed) : Measure Seed :=
  (incoming.prod (Measure.pi drawLaw)).map (adaptiveSeedStep next)

instance adaptiveSeedLaw_probability (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (next : ∀ seed, Draw seed → Seed) : IsProbabilityMeasure (adaptiveSeedLaw drawLaw incoming next) := by
  unfold adaptiveSeedLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Step

section Sequence

variable {Seed : Type*} [Fintype Seed] [DecidableEq Seed]
  [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  {Draw : ℕ → Seed → Type*} [∀ pass seed, Fintype (Draw pass seed)]
  [∀ pass seed, MeasurableSpace (Draw pass seed)]
  [∀ pass seed, MeasurableSingletonClass (Draw pass seed)]
  (drawLaw : ∀ pass seed, Measure (Draw pass seed))
  [∀ pass seed, IsProbabilityMeasure (drawLaw pass seed)]
  (incoming : Measure Seed) (next : ∀ pass seed, Draw pass seed → Seed)

noncomputable def adaptiveSeedSequence : ℕ → Measure Seed
  | 0 => incoming
  | pass + 1 => adaptiveSeedLaw (drawLaw pass) (adaptiveSeedSequence pass) (next pass)

instance adaptiveSeedSequence_probability [IsProbabilityMeasure incoming] (pass : ℕ) :
    IsProbabilityMeasure (adaptiveSeedSequence drawLaw incoming next pass) := by
  induction pass with
  | zero => exact inferInstanceAs (IsProbabilityMeasure incoming)
  | succ pass ih =>
    let := ih
    exact inferInstanceAs (IsProbabilityMeasure
      (adaptiveSeedLaw (drawLaw pass) (adaptiveSeedSequence drawLaw incoming next pass) (next pass)))

end Sequence

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_CommonRangeSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The online draw range depends on earlier seed values. A common random
source is indexed by the physical key and the requested positive range,
not by an entire hypothetical seed table. The unused coordinates exist
only in the probability space. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory






theorem positiveDrawRangeOfLE_val (B n : ℕ) (hn : 0 < n) (hB : n ≤ B) :
    (positiveDrawRangeOfLE B n hn hB).val.val = n := rfl



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCurrentQueryBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial same-index call budget after substituting the
computed window, cell, scale-label, sampling and rounding parameters. -/

namespace EditApproximation

def localCurrentBudget (window cells labels M Q inverseTheta : ℕ) : ℕ :=
  window * cells * labels * (624 * M * Q * inverseTheta ^ 2) + window * cells * M + window * M

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_EarlierInputBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit wide-history cover fits the polynomial earlier-input
budget used in the dependency-path count. -/

namespace EditApproximation

def localEarlierBudget (window cells M P F history : ℕ) : ℕ :=
  window * ((64 * F * P + 2) ^ 2 + cells * (P + 1) ^ 2 + 1) *
    M * history * (40 * P + 2) ^ 2

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalOnlineKeys
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Online random streams have bounded physical keys. The embedding of
the complete representative table is used only in the proof of the law;
the local program requests the scale and rounded center directly. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory





theorem physicalScaleIndex_get (N b : ℕ) (hb : b ∈ dyadicScales N) :
    (dyadicScales N).get (physicalScaleIndex N b hb) = b :=
  List.getElem_idxOf (List.idxOf_lt_length_of_mem hb)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalGroupSourceQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Whole-cell group samples are exposed through scalar source reads.
Every needed scale/sample coordinate is enumerated once per group; unused
groups are absent from this query. -/

namespace EditApproximation





theorem groupScalarKeys_mem (M F Q : ℕ) (groups : List (ℕ × (ℕ × ℕ)))
    (key : ℕ × (ℕ × ℕ)) (hk : key ∈ groups)
    (scale : Fin (groupDyadicScales M key.1 F).length)
    (sample : Fin (groupSampleCount M Q key.1 (groupDyadicScaleAt M key.1 F scale))) :
    (⟨key, scale, sample⟩ : GroupScalarKey M F Q) ∈ groupScalarKeys M F Q groups := by
  apply List.mem_flatMap.mpr
  refine ⟨key, hk, List.mem_flatMap.mpr ?_⟩
  exact ⟨scale, List.mem_finRange _, List.mem_map.mpr ⟨sample, List.mem_finRange _, rfl⟩⟩

def groupScalarValue {M F Q : ℕ} (draw : CellGroupDraws M F Q) (key : GroupScalarKey M F Q) : ℚ :=
  (draw key.1.1 key.1.2 key.2.1 key.2.2).val



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalRandomQueryKeys
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

namespace FiniteQuery

theorem keys_all_mapKeys {ι κ : Type*} (f : ι → κ) (query : FiniteQuery ι)
    (oracle : κ → ℚ) (predicate : κ → Prop)
    (h : ∀ key ∈ query.keys (oracle ∘ f), predicate (f key)) :
    ∀ key ∈ (mapKeys f query).keys oracle, predicate key := by
  rw [mapKeys_keys]
  intro key hk
  obtain ⟨other, ho, rfl⟩ := List.mem_map.mp hk
  exact h other ho

end FiniteQuery

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_OccurrenceIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A symbol dictionary of cached position tries. The target is enumerated
once; interval occurrence queries use two logarithmic prefix counts. -/

namespace EditApproximation

def occurrencePrefixCount : List (ℕ × ℕ) → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | e :: es, a, t => occurrencePrefixCount es a t + if e.1 = a ∧ e.2 < t then 1 else 0

def occurrenceRangeCount : List (ℕ × ℕ) → ℕ → ℕ → ℕ → ℕ
  | [], _, _, _ => 0
  | e :: es, a, lo, hi => occurrenceRangeCount es a lo hi +
      if e.1 = a ∧ lo ≤ e.2 ∧ e.2 < hi then 1 else 0

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PrefixBitEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-degree polynomial envelope for the literal prefix and band-test
arithmetic. The finite expression represents the bit counters;
its degree is independent of every input length and parameter. -/

namespace EditApproximation

def prefixEnv (M j v B : ℕ) : Fin 4 → ℕ
  | 0 => M
  | 1 => j
  | 2 => v
  | _ => B

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PreparedBandPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed-degree bound for the complete band constructor. The sole
non-polynomial quantity is the actual Cartesian-product list bound, an
explicit input subsequently bounded by the computed grid parameters. -/

namespace EditApproximation

def preparedBandEnvironment (e b M P v w B : ℕ) : Fin 8 → ℕ
  | 0 => M
  | 1 => P
  | 2 => e
  | 3 => Nat.size b
  | 4 => v
  | 5 => w
  | 6 => B
  | _ => ((40 * P + 2) ^ 2 + 1) ^ (M + 1)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PreparedGroupPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed-degree cap for the complete cell selector, including all band
construction and exact finite-count sampled scores. -/

namespace EditApproximation

def cellGroupEnvironment (M P B X : ℕ) : Fin 4 → ℕ
  | 0 => M
  | 1 => P
  | 2 => B
  | _ => X

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PreparedLocalGroupPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed-degree cap on all whole-cell loops at a query. Distance scales
enter through their bit length; their numeric size is never charged. -/

namespace EditApproximation

def localGroupEnvironment (F thetaPow B eM eF X : ℕ) : Fin 8 → ℕ
  | 0 => F
  | 1 => thetaPow
  | 2 => B
  | 3 => eM
  | 4 => eF
  | 5 => X
  | _ => 0

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PreparedCachedKernelWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete refinement return includes literal power-denominator
construction, multiplication, division and trimming before cache insertion. -/

namespace EditApproximation

def cacheEnvironment (M B n D : ℕ) : Fin 4 → ℕ
  | 0 => M
  | 1 => B
  | 2 => n
  | _ => D

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SourceRankedProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Random source coordinates and recursive table entries share the same
memo evaluator. Source coordinates have rank zero; each table rank is
shifted by one. Consequently repeated source reads reuse their stored draw. -/

namespace EditApproximation

namespace SourceRanked

variable {σ κ : Type*}







def value (sourceValue : σ → ℚ) (tableValue : κ → ℚ) : Sum σ κ → ℚ :=
  Sum.elim sourceValue tableValue

end SourceRanked

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SourceErasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing already fixed source answers is a proof operation on a
query. It preserves the table trace and separates source/table charges;
the implementation continues to cache and sample explicit source keys. -/

namespace EditApproximation.FiniteQuery

variable {σ κ : Type*}

def eraseSources (sourceAnswer : σ → ℚ) : FiniteQuery (Sum σ κ) → FiniteQuery κ
  | .done value => .done value
  | .read (.inl source) next => eraseSources sourceAnswer (next (sourceAnswer source))
  | .read (.inr table) next => .read table (fun answer => eraseSources sourceAnswer (next answer))

 theorem eraseSources_value (sourceAnswer : σ → ℚ) (tableAnswer : κ → ℚ)
    (query : FiniteQuery (Sum σ κ)) :
    (eraseSources sourceAnswer query).value tableAnswer =
      query.value (Sum.elim sourceAnswer tableAnswer) := by
  induction query with
  | done value => rfl
  | read key next ih =>
    cases key with
    | inl source => exact ih (sourceAnswer source)
    | inr table => exact ih (tableAnswer table)

 theorem eraseSources_keys_all (sourceAnswer : σ → ℚ) (tableAnswer : κ → ℚ)
    (query : FiniteQuery (Sum σ κ)) (predicate : κ → Prop)
    (hquery : ∀ key ∈ query.keys (Sum.elim sourceAnswer tableAnswer),
      match key with | .inl _ => True | .inr table => predicate table) :
    ∀ key ∈ (eraseSources sourceAnswer query).keys tableAnswer, predicate key := by
  induction query with
  | done value => intro key hk; exact False.elim (List.not_mem_nil hk)
  | read key next ih =>
    cases key with
    | inl source =>
      apply ih (sourceAnswer source)
      intro key hk
      exact hquery key (List.mem_cons_of_mem _ hk)
    | inr table =>
      intro key hk
      rcases List.mem_cons.mp hk with heq | hk
      · subst key
        exact hquery (.inr table) (List.mem_cons_self ..)
      · apply ih (tableAnswer table) _ key hk
        intro key hk
        exact hquery key (List.mem_cons_of_mem _ hk)

end EditApproximation.FiniteQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RankedMemoKeys
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A cache miss is among the requests of the uncached execution with
identical answers. This includes adaptive continuations and cache hits. -/

namespace EditApproximation

def rankedUncachedKeys {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key}) (key : κ) : List κ :=
  key :: ((program key).keys (fun child => rankedProgramValue rank program child.val)).flatMap
    (fun child => rankedUncachedKeys rank program child.val)
termination_by rank key
decreasing_by exact child.property

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SourceRankedWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Source leaves add only their executed read count to each table body.
Projecting them away preserves the table dependency program, so a uniform
local source budget multiplies its uncached request bound. -/

namespace EditApproximation.SourceRanked

variable {σ κ : Type*} (tableRank : κ → ℕ)
  (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
  (sourceValue : σ → ℚ) (tableValue : κ → ℚ)
  (hbody : ∀ key, (tableBody key).value (Sum.elim sourceValue (fun next => tableValue next.val)) =
    tableValue key)

def projectedBody (key : κ) : FiniteQuery {next : κ // tableRank next < tableRank key} :=
  FiniteQuery.eraseSources sourceValue (tableBody key)

include hbody in
 theorem projectedBody_value (key : κ) :
    (projectedBody tableRank tableBody sourceValue key).value (fun next => tableValue next.val) =
      tableValue key :=
  (FiniteQuery.eraseSources_value sourceValue _ (tableBody key)).trans (hbody key)

end EditApproximation.SourceRanked

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_BernsteinEnvelope
attribute [-instance] _root_.OAI.EditApproximation.physicalFamilyRange_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar exponential estimate used to discharge the finite Bernstein
input. Its rational majorant is proved by a derivative comparison, avoiding
any assumption of a concentration theorem. -/

namespace EditApproximation

noncomputable def bernsteinEnvelope (x : ℝ) : ℝ :=
  Real.exp (-x) * ((x ^ 2 + 4 * x + 6) / (6 - 2 * x))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_RejectionSelectedCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Rejection counts are independent of all accepted values. Thus even
an adaptive choice of coordinates incurs fewer than two word trials per
selected coordinate in expectation. No unused source is charged. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Selected

variable {ι : Type*} [Fintype ι] (range : ι → ℕ) [∀ i, NeZero (range i)]



instance rejectionAcceptedLaw_probability : IsProbabilityMeasure (rejectionAcceptedLaw range) := by
  unfold rejectionAcceptedLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)



instance rejectionFailureLaw_probability (i : ι) : IsProbabilityMeasure (rejectionFailureLaw range i) := by
  unfold rejectionFailureLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)





instance rejectionRuntimeArrayLaw_probability : IsProbabilityMeasure (rejectionRuntimeArrayLaw range) := by
  unfold rejectionRuntimeArrayLaw rejectionAcceptedLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end Selected

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteProductWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The executed sampler law supports both selected rejection work and
work depending only on the accepted finite draws. -/

namespace EditApproximation
open MeasureTheory

section Accepted
variable {α ι : Type*} [Fintype α] [Fintype ι]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  (range : ι → ℕ) [∀ i, NeZero (range i)]
  (μ : Measure α) [IsFiniteMeasure μ]

 def rejectionProductAccepted (outcome : α × RejectionRuntimeArray range) : α × (∀ i, Fin (range i)) :=
  (outcome.1, outcome.2.2)

end Accepted
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteSeedFinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The final fresh draw selects the coordinate of the actual incoming seed.
This keeps the dependence of the finite draw type on that table explicit. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Final

variable {Seed : Type*} [Fintype Seed]
  [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  {Draw : Seed → Type*} [∀ seed, Finite (Draw seed)]
  [∀ seed, MeasurableSpace (Draw seed)] [∀ seed, MeasurableSingletonClass (Draw seed)]
  (drawLaw : ∀ seed, Measure (Draw seed)) [∀ seed, IsProbabilityMeasure (drawLaw seed)]
  (incoming : Measure Seed) [IsProbabilityMeasure incoming]

def freshSeedValue (value : ∀ seed, Draw seed → ℝ)
    (pair : Seed × (∀ seed, Draw seed)) : ℝ := value pair.1 (pair.2 pair.1)

end Final

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryDependencyExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dependency tree here is obtained from the requests made by the
finite adaptive program at its actual answers. Local depth/index progress
therefore bounds execution, rather than an independently supplied tree. -/

namespace EditApproximation

open Finset

section Queries

variable {κ : Type*} (depth index : κ → ℕ)
  (program : (key : κ) → FiniteQuery
    {child : κ // depth child + index child < depth key + index key})

def queryRequestList (key : κ) : List κ :=
  ((program key).keys (fun child =>
    rankedProgramValue (fun x => depth x + index x) program child.val)).map Subtype.val

def querySameRequests (key : κ) : List κ :=
  (queryRequestList depth index program key).filter (fun child => !(index child < index key))

def queryEarlierRequests (key : κ) : List κ :=
  (queryRequestList depth index program key).filter (fun child => index child < index key)

variable (progress : ∀ key child, child ∈ queryRequestList depth index program key →
  (depth child < depth key ∧ index child ≤ index key) ∨
  (depth child ≤ depth key ∧ index child < index key))

include progress

theorem querySameRequests_progress (key : κ)
    (i : Fin (querySameRequests depth index program key).length) :
    depth ((querySameRequests depth index program key).get i) < depth key ∧
      index ((querySameRequests depth index program key).get i) ≤ index key := by
  have hm := List.mem_filter.mp (List.get_mem (querySameRequests depth index program key) i)
  have hnot : ¬ index ((querySameRequests depth index program key).get i) < index key := by
    simpa using hm.2
  rcases progress key _ hm.1 with h | h
  · exact h
  · exact False.elim (hnot h.2)

theorem queryEarlierRequests_progress (key : κ)
    (i : Fin (queryEarlierRequests depth index program key).length) :
    depth ((queryEarlierRequests depth index program key).get i) ≤ depth key ∧
      index ((queryEarlierRequests depth index program key).get i) < index key := by
  have hm := List.mem_filter.mp (List.get_mem (queryEarlierRequests depth index program key) i)
  have hi : index ((queryEarlierRequests depth index program key).get i) < index key := by
    simpa only [decide_eq_true_eq] using hm.2
  refine ⟨?_, hi⟩
  rcases progress key _ hm.1 with h | h
  · exact h.1.le
  · exact h.1

end Queries

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryWeightedWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Per-request local work summed along the actual adaptive expansion.
This is a weighted analogue of the uncached request count. -/

namespace EditApproximation

open Finset

def rankedUncachedWork {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (weight : κ → ℕ) (key : κ) : ℕ :=
  (program key).cost (fun child => rankedProgramValue rank program child.val)
    (fun child => rankedUncachedWork rank program weight child.val) + weight key
termination_by rank key
decreasing_by exact child.property

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedWarmupReadBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial earlier-edge bound for the complete charged warmup
query. It includes all preceding-pass copy reads and pass-zero coarse
reads used by its initial cones. -/

namespace EditApproximation

def warmupReadBudget (scales window P F Amax M copies : ℕ) : ℕ :=
  (1 + window * (64 * F * P + 2) ^ 2) *
    ((1 + scales * (64 * Amax ^ 2 * P + 2) ^ 2) * max 1 copies) +
    window * (64 * F * P + 2) ^ 2 * M * (40 * P + 2) ^ 2

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalGroupKeys
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Every whole-cell stream used by the complete program has a bounded
physical key. Its two cell coordinates are at most n*2^exponent. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

theorem targetCell_coordinate_bound {n : ℕ} (exponent b : ℕ) (hb : 1 ≤ b)
    (q : TargetInterval n) :
    (targetCell ((2 : ℚ) ^ (-(exponent : ℤ)) * b) q).1 ≤ n * 2 ^ exponent ∧
    (targetCell ((2 : ℚ) ^ (-(exponent : ℤ)) * b) q).2 ≤ n * 2 ^ exponent := by
  have hside : (0 : ℚ) < (2 : ℚ) ^ (-(exponent : ℤ)) * b := by positivity
  have hcoordinate (p : ℕ) (hp : p ≤ n) :
      ⌊(p : ℚ) / ((2 : ℚ) ^ (-(exponent : ℤ)) * b)⌋₊ ≤ n * 2 ^ exponent := by
    have hcancel : ((n * 2 ^ exponent : ℕ) : ℚ) *
        ((2 : ℚ) ^ (-(exponent : ℤ)) * b) = n * b := by
      push_cast
      rw [zpow_neg, zpow_natCast]
      field_simp
    have hmul : (p : ℚ) ≤ ((n * 2 ^ exponent : ℕ) : ℚ) *
        ((2 : ℚ) ^ (-(exponent : ℤ)) * b) := by
      rw [hcancel]
      exact_mod_cast hp.trans (Nat.le_mul_of_pos_right n (by omega))
    have h := Nat.floor_le_floor ((div_le_iff₀ hside).2 hmul)
    simpa only [Nat.floor_natCast] using h
  exact ⟨hcoordinate q.lo (q.ordered.trans q.valid), hcoordinate q.hi q.valid⟩



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLocalProgramLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single bounded-key product supplies both online and whole-cell
streams. Restriction to the complete program preserves their joint law,
including independence between the two kinds of stream. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

abbrev PhysicalLocalProgramKey (M J N n exponent : ℕ) :=
  Sum (PhysicalLocalOnlineKey M J N n) (PhysicalLocalGroupKey M J N n exponent)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalScalarSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Each common array source is realized by scalar exact uniform draws.
Regrouping finite coordinates recovers the common source law; unused
coordinates belong only to the probability space. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory











abbrev PhysicalScalarDraw (M J N n exponent F Q R B : ℕ) :=
  ∀ key : PhysicalScalarKey M J N n exponent F Q R B,
    Fin (physicalScalarRange M J N n exponent F Q R B key)

noncomputable def physicalScalarLaw (M J N n exponent F Q R B : ℕ) [NeZero M] :
    Measure (PhysicalScalarDraw M J N n exponent F Q R B) :=
  Measure.pi fun key => (PMF.uniformOfFintype
    (Fin (physicalScalarRange M J N n exponent F Q R B key))).toMeasure

instance physicalScalarLaw_probability (M J N n exponent F Q R B : ℕ) [NeZero M] :
    IsProbabilityMeasure (physicalScalarLaw M J N n exponent F Q R B) := by
  unfold physicalScalarLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalScalarReads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Direct scalar source requests. The physical scale/cell guards agree
with the original raw providers, and an online request carries its range. -/

namespace EditApproximation

section Reads

variable (M J N n exponent F Q R B : ℕ) [NeZero M]



def physicalScalarAnswer (draw : PhysicalScalarDraw M J N n exponent F Q R B)
    (key : PhysicalScalarKey M J N n exponent F Q R B) : ℚ := (draw key).val









end Reads

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalScalarFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Finite independent scalar sources for all passes and copies. The
incoming seed selects the range only after the earlier passes are evaluated. -/

namespace EditApproximation

section Family

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ) (hP : 0 < P)





variable (draw : PhysicalFamilyScalarDraw
  (M := M) (J := J) (R := R) target N P F exponent H Q passes copies)

def physicalFamilyDraw (pass copy : ℕ) :
    PhysicalScalarDraw M J N target.length exponent F Q R (localOnlineMassBound M P H) :=
  fun key => draw (Fin.ofNat (passes + 1) pass, Fin.ofNat (copies + 1) copy, key)







end Family

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalScalarFamilyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regrouping the finite physical scalar source gives exactly one fresh
common draw for each pass and copy. This is equality of product laws,
not an assumption about the sampler. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section FamilyLaw

variable {α : Type*} {M J R : ℕ} [NeZero M]
  (target : List α) (N P F exponent H Q passes copies : ℕ)

def physicalFamilyCurry (draw : PhysicalFamilyScalarDraw
    (M := M) (J := J) (R := R) target N P F exponent H Q passes copies)
    (pass : Fin (passes + 1)) (copy : Fin (copies + 1)) :
    PhysicalScalarDraw M J N target.length exponent F Q R (localOnlineMassBound M P H) :=
  fun key => draw (pass, copy, key)

end FamilyLaw

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedPhysicalUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

open MeasureTheory ProbabilityTheory

theorem computedParameterP_pos (N : ℕ) : 0 < (integerParameters N).P :=
  Nat.pow_pos (Nat.two_pow_pos _)









end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedWidthEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A parameter-only majorant for every executed dependency tree. It is
independent of the accepted random values and of all accuracy events. -/

namespace EditApproximation

open Filter
open scoped Topology

noncomputable def computedWidthEnvelope (N : ℕ) : ℝ :=
  (N + 2 : ℝ) * (inputHeight N : ℝ) ^ 2 *
    Real.exp (computedDependencyOverheadExponent 257 512 N)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedLocalKernelWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter
open scoped Topology

 def localKernelPowerExponent (M p D : ℕ) : ℕ := ((100 * M + 100000) * (p + 1)) * D

 def computedLocalKernelBudget (D N : ℕ) : ℕ :=
  inputHeight N ^ localKernelPowerExponent (integerParameters N).M
    (coarseExponent (inputSmallLog N)) D

noncomputable def computedLocalKernelExponent (D N : ℕ) : ℝ :=
  (D : ℝ) * ((100 * Real.log 2) * ((integerParameters N).M : ℝ) *
      ((coarseExponent (inputSmallLog N) : ℝ) + 1) * inputSmallLog N +
    100000 * ((coarseExponent (inputSmallLog N) : ℝ) + 1) * Real.log (inputHeight N : ℝ))

end EditApproximation

end OAI
end


