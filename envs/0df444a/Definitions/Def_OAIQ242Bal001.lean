-- Prove2me | Definitions.Def_OAIQ242Bal001
-- name    : OAIQ242Bal001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:44:05.118048+00:00
-- url     : https://prove2.me/theorems/bc83200b-190b-4791-a5e6-70651aa2f6aa
-- title:
--   Definitions bundle OAIQ242Bal001 of the split of OpenAI, Directional transience implies ballisticity
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 314 declarations of OpenAI's Lean: 159 definitions, 23 instances and 132 theorems. The definitions and types are `OAI.DirectionalTransience.FirstBelow`, `OAI.DirectionalTransience.FirstPairTest`, `OAI.DirectionalTransience.FullNormalJointPast`, `OAI.DirectionalTransience.GridLinear`, `OAI.DirectionalTransience.GridOscillation`, `OAI.DirectionalTransience.HeightBlockRelation`, `OAI.DirectionalTransience.HeightGapEvent`, `OAI.DirectionalTransience.HeightOscillation`, `OAI.DirectionalTransience.IsIntegerMedian`, `OAI.DirectionalTransience.JointPastTimes`, `OAI.DirectionalTransience.NormalJointPast`, `OAI.DirectionalTransience.NormalSinglePast`, `OAI.DirectionalTransience.RapidDecay`, `OAI.DirectionalTransience.RealPathPair`, `OAI.DirectionalTransience.ReferenceClasses.UpperField`, `OAI.DirectionalTransience.ReferenceClasses.dustFrequency`, `OAI.DirectionalTransience.SeparatedCrossBound`, `OAI.DirectionalTransience.StageRadiusOrder`, `OAI.DirectionalTransience.StationaryCompact.episodeOccupation`, `OAI.DirectionalTransience.StationaryCompact.episodeOccupationRaw`, `OAI.DirectionalTransience.StoppedWindow.selectedKernel`, `OAI.DirectionalTransience.TransientPaths`, `OAI.DirectionalTransience.TupleKernel.dependentPair`, `OAI.DirectionalTransience.absSlope`, `OAI.DirectionalTransience.bandTruncate`, `OAI.DirectionalTransience.bufferNextRadius`, `OAI.DirectionalTransience.bufferRestoreLength`, `OAI.DirectionalTransience.bufferRetentionCost`, `OAI.DirectionalTransience.bufferWordHeight`, `OAI.DirectionalTransience.canonicalLogExcess`, `OAI.DirectionalTransience.capExcessTest`, `OAI.DirectionalTransience.cappedExp`, `OAI.DirectionalTransience.cappedLogLoss`, `OAI.DirectionalTransience.cappedMoment`, `OAI.DirectionalTransience.cappedTailMoment`, `OAI.DirectionalTransience.cellAttemptSuccess`, `OAI.DirectionalTransience.cellEarlyHeight`, `OAI.DirectionalTransience.cellLateHeight`, `OAI.DirectionalTransience.cellOpportunity`, `OAI.DirectionalTransience.cellWidth` and 119 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `Ballisticity_Coupling_FreshPolicyIndependence`, `Ballisticity_Coupling_SeedIteration`, `Ballisticity_Coupling_SeedMedian`, `Ballisticity_Crossings_ContinuousCrossPast`, `Ballisticity_Crossings_CutoffTimeAverages`, `Ballisticity_Crossings_Hit`, `Ballisticity_Crossings_NearCrossEstimates`, `Ballisticity_Crossings_PastCutoffs`, `Ballisticity_Crossings_TailCuts`, `Ballisticity_Entropy_CanonicalLogExcess`, `Ballisticity_Entropy_DominatedEntropy`, `Ballisticity_Entropy_StoppedWindowEntropy`, `Ballisticity_Estimates_AdaptiveFailureWeights`, `Ballisticity_Estimates_AlignedRecordPrefix`, `Ballisticity_Estimates_AllLayerOccupation`, `Ballisticity_Estimates_BoundaryDecorrelation`, `Ballisticity_Estimates_BoundedAnchorAverage`, `Ballisticity_Estimates_BufferChildNode`, `Ballisticity_Estimates_CappedExp`, `Ballisticity_Estimates_CappedLoss`, `Ballisticity_Estimates_CappedMomentTransfer`, `Ballisticity_Estimates_CellAttempt`, `Ballisticity_Estimates_CellExhaustion`, `Ballisticity_Estimates_CellFailure`, `Ballisticity_Estimates_CellRadiusComparison`, `Ballisticity_Estimates_CellSchedule`, `Ballisticity_Estimates_CharacteristicProductLaw`, `Ballisticity_Estimates_CharacteristicTaylor`, `Ballisticity_Estimates_ClassSelection`, `Ballisticity_Estimates_ClippedAbsThreeHalves`, `Ballisticity_Estimates_ClippedInverse`, `Ballisticity_Estimates_ClippedThreeHalves`, `Ballisticity_Estimates_CommonWidthProcess`, `Ballisticity_Estimates_CommonWordIncrement`, `Ballisticity_Estimates_ConditionalLawTests`, `Ballisticity_Estimates_CountableProdBind`, `Ballisticity_Estimates_CurvePolicyAlignment`, `Ballisticity_Estimates_CurvePolicyPMF`, `Ballisticity_Estimates_EventRate`, `Ballisticity_Estimates_FavorablePairFraction`, `Ballisticity_Estimates_FinitePastDecorrelation`, `Ballisticity_Estimates_FinitePolicyPMF`, `Ballisticity_Estimates_FiniteStage`, `Ballisticity_Estimates_FirstBelow`, `Ballisticity_Estimates_FluctuationScaleUpperMultiple`, `Ballisticity_Estimates_GridLinear`, `Ballisticity_Estimates_GridOccupation`, `Ballisticity_Estimates_GridOscillation`, `Ballisticity_Estimates_IidListProcess`, `Ballisticity_Estimates_IndependentDyadic`, `Ballisticity_Estimates_IntegerMedian`, `Ballisticity_Estimates_InteriorPairMeasureExt`, `Ballisticity_Estimates_JointPastMoments`, `Ballisticity_Estimates_LocalStoppedSplice`, `Ballisticity_Estimates_LowerClip`, `Ballisticity_Estimates_MomentRescaling`, `Ballisticity_Estimates_NonCollapsedSums`, `Ballisticity_Estimates_NormalLinearPast`, `Ballisticity_Estimates_ObservedPotential`, `Ballisticity_Estimates_OccupationAlgebra`, `Ballisticity_Estimates_OrderedTimes`, `Ballisticity_Estimates_PastPhaseExtension`, `Ballisticity_Estimates_ProductNormalJointPast`, `Ballisticity_Estimates_ProfileMeasureUpdate`, `Ballisticity_Estimates_ProtectionFirstFailure`, `Ballisticity_Estimates_ProtectionLoss`, `Ballisticity_Estimates_RadixBudget`, `Ballisticity_Estimates_RapidDecay`, `Ballisticity_Estimates_RecordIndexTime`, `Ballisticity_Estimates_ReferenceContinuity`, `Ballisticity_Estimates_RelativeBudget`, `Ballisticity_Estimates_RestartLyapunov`, `Ballisticity_Estimates_Sampling`, `Ballisticity_Estimates_SelectedEndpointMoment`, `Ballisticity_Estimates_SharedLimitNormalPast`, `Ballisticity_Estimates_SmallScaleGaussianMass`, `Ballisticity_Estimates_StoppedSplice`, `Ballisticity_Estimates_SuccessfulScaledTail`, `Ballisticity_Estimates_SymmetricTruncate`, `Ballisticity_Estimates_TailProfile`, `Ballisticity_Estimates_TailSampling`, `Ballisticity_Estimates_UniformRiemannMesh`, `Ballisticity_Estimates_WordDepartures`, `Ballisticity_Geometry_BufferElapsedHeight`, `Ballisticity_Geometry_HeightIncrement`, `Ballisticity_Geometry_HeightPolygon`, `Ballisticity_Geometry_HeightTubeWindow`, `Ballisticity_Geometry_WordHeightGain`, `Ballisticity_Stationary_Array`, `Ballisticity_Stationary_ArrayMap`, `Ballisticity_Stationary_ArrayMarkTests`, `Ballisticity_Stationary_ArrayMassSurvival`, `Ballisticity_Stationary_ArrayTopology`, `Ballisticity_Stationary_EpisodeExponential`, `Ballisticity_Stationary_EpisodeRetention`, `Ballisticity_Stationary_StationaryCompact`, `Ballisticity_Stationary_StationaryMarking`, `Ballisticity_Stationary_StationaryMonotone`, `Ballisticity_Walk_ArrayGrowthEvent`, `Ballisticity_Walk_GaussianPathFiniteLawSmul`, `Ballisticity_Walk_PathPointMean`, `Ballisticity_Walk_PathWindowTest`, `Ballisticity_Walk_ProfileGrowth`, `Ballisticity_Walk_Rows`, `Ballisticity_Walk_SelectedFiniteKernel`, `Ballisticity_Walk_StateTrajectory`, `Ballisticity_Walk_StationaryGrowth`, `Ballisticity_Walk_TailGrowth`, `Ballisticity_Walk_UniformFinsetKernel`.
--
--   **Imports.** It imports the published bundle `Def_DirectionalBallisticity`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ242Bal002` and `OAIQ242Bal003`; the statements `OAI.DirectionalTransience.crossing_failure_rapidDecay`, `OAI.DirectionalTransience.height_median_path_limit` and `OAI.DirectionalTransience.normalJointPast_product_identification`; the proofs of `OAI.DirectionalTransience.height_median_path_limit` and `OAI.DirectionalTransience.normalJointPast_product_identification`.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_DirectionalBallisticity

section
-- module Solutions.OAIQ242_BAL.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FinitePolicyPMF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def finitePolicyPMF {Ω G : Type*} [Add G]
    (Q : ℕ → Ω → G → PMF G) (ω : Ω) (i : ℕ) (x : G) : ℕ → PMF (List G)
  | 0 => PMF.pure []
  | n+1 => (Q i ω x).bind fun u => (finitePolicyPMF Q ω (i+1) (x+u) n).map (List.cons u)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_StateTrajectory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace DirectionalTransience

instance environmentLaw_probability {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (environmentLaw ν) := by
  unfold environmentLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance initialLaw_probability {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (initialLaw ν) := by
  unfold initialLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance annealedLaw_probability {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (annealedLaw ν) := by
  unfold annealedLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma environment_uniform_elliptic {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) :
    ∃ κ : ℝ≥0, 0 < κ ∧ ∀ᵐ ω ∂environmentLaw ν, ∀ x e, κ ≤ (ω x).1 e := by
  obtain ⟨κ, hκ, hrows⟩ := hue
  refine ⟨κ, hκ, ae_all_iff.mpr fun x => ?_⟩
  exact (measurePreserving_eval_infinitePi (fun _ : Lattice d => ν) x).quasiMeasurePreserving.ae hrows

lemma row_entry_le_one {d : ℕ} (p : Row d) (e : Direction d) : p.1 e ≤ 1 := by
  calc
    p.1 e ≤ ∑ i, p.1 i := Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ e)
    _ = 1 := p.2

lemma environment_translation {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (z : Lattice d) :
    (environmentLaw ν).map (fun ω x => ω (z + x)) = environmentLaw ν := by
  apply Measure.map_infinitePi_infinitePi_of_inj
  exact add_right_injective z

instance state_measurableEq {d : ℕ} : MeasurableEq (State d) where
  measurableSet_diagonal := by
    change MeasurableSet {zz : State d × State d | zz.1 = zz.2}
    simp only [Prod.ext_iff, Set.ofPred_and]
    exact (measurableSet_eq_fun (measurable_fst.comp measurable_fst)
      (measurable_fst.comp measurable_snd)).inter
      (measurableSet_eq_fun (measurable_snd.comp measurable_fst)
        (measurable_snd.comp measurable_snd))

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_FreshPolicyIndependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def futureRows {d : ℕ} (S : ℕ → Set (Lattice d)) (i : ℕ) : Set (Lattice d) :=
  ⋃ j ∈ Set.Ici i, S j

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_WordDepartures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma tendsto_atTop_has_minimum (a : ℕ → ℝ) (ha : Tendsto a atTop atTop) :
    ∃ n, ∀ j, a n ≤ a j := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ha.eventually (eventually_ge_atTop (a 0)))
  obtain ⟨n, hn, hmin⟩ := Finset.exists_min_image (Finset.range (N + 1)) a
    ⟨0, by simp⟩
  refine ⟨n, fun j => ?_⟩
  by_cases hj : N ≤ j
  · exact (hmin 0 (by simp)).trans (hN j hj)
  · exact hmin j (Finset.mem_range.mpr (by omega))

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_Hit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

def TransientPaths {d : ℕ} (ℓ : Vector d) : Set (Path d) :=
  {X | Tendsto (fun n => dot (realPosition (X n)) ℓ) atTop atTop}

lemma mass_of_small_mean {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → ℝ≥0∞) (hf : Measurable f)
    {s : ℝ≥0} (hs : 0 < s) (hmean : (∫⁻ a, f a ∂μ) ≤ (s : ℝ≥0∞)) :
    (1 : ℝ≥0∞) ≤ 2 * μ {a | f a ≤ 2 * (s : ℝ≥0∞)} := by
  let B := {a | f a ≤ 2 * (s : ℝ≥0∞)}
  let G := {a | 2 * (s : ℝ≥0∞) ≤ f a}
  have hcover : (1 : ℝ≥0∞) ≤ μ B + μ G := by
    calc
      1 = μ Set.univ := (measure_univ).symm
      _ ≤ μ (B ∪ G) := measure_mono (fun a _ => le_total (f a) (2 * (s : ℝ≥0∞)))
      _ ≤ μ B + μ G := measure_union_le _ _
  have hmark : (2 * (s : ℝ≥0∞)) * μ G ≤ (s : ℝ≥0∞) :=
    (mul_meas_ge_le_lintegral₀ hf.aemeasurable _).trans hmean
  have hc := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top μ B, measure_ne_top μ G⟩) hcover
  have hm := ENNReal.toReal_mono ENNReal.coe_ne_top hmark
  rw [ENNReal.toReal_one, ENNReal.toReal_add (measure_ne_top μ B) (measure_ne_top μ G)] at hc
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.coe_toReal] at hm
  apply (ENNReal.toReal_le_toReal (by norm_num)
    (ENNReal.mul_ne_top (by norm_num) (measure_ne_top μ B))).mp
  simp only [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_ofNat]
  have hsreal : (0 : ℝ) < s := by exact_mod_cast hs
  change 1 ≤ 2 * (μ B).toReal
  nlinarith

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FirstBelow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

def FirstBelow {α : Type*} [Preorder α] (a : ℕ → α) (t : α) (n : ℕ) : Prop :=
  a n < t ∧ ∀ k < n, t ≤ a k

lemma firstBelow_iff_exists {α : Type*} [LinearOrder α] (a : ℕ → α) (t : α) :
    (∃ n, FirstBelow a t n) ↔ ∃ n, a n < t := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.1⟩
  · intro h
    exact ⟨Nat.find h, Nat.find_spec h, fun k hk => le_of_not_gt (Nat.find_min h hk)⟩

lemma firstBelow_unique {α : Type*} [LinearOrder α] {a : ℕ → α} {t : α} {n m : ℕ}
    (hn : FirstBelow a t n) (hm : FirstBelow a t m) : n = m := by
  rcases lt_trichotomy n m with h | h | h
  · exact False.elim ((not_lt_of_ge (hm.2 n h)) hn.1)
  · exact h
  · exact False.elim ((not_lt_of_ge (hn.2 m h)) hm.1)

lemma firstBelow_pairwise_disjoint {α β : Type*} [LinearOrder β] (a : ℕ → α → β) (t : β) :
    Pairwise (fun n m => Disjoint {ω | FirstBelow (fun k => a k ω) t n}
      {ω | FirstBelow (fun k => a k ω) t m}) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro ω hn hm
  exact hnm (firstBelow_unique (a := fun k => a k ω) hn hm)

lemma positive_random_small_set {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (f : α → ℝ≥0∞) (hf : Measurable f)
    (hp : ∀ᵐ x ∂μ, 0 < f x) :
    ∃ s : ℝ≥0, 0 < s ∧ s ≤ 1 / 4 ∧ μ {x | f x ≤ 2 * (s : ℝ≥0∞)} < 1 / 4 := by
  let b : ℝ≥0 := 1 / 2
  let E := fun n : ℕ => {x | f x ≤ ((b ^ n : ℝ≥0) : ℝ≥0∞)}
  have hE (n : ℕ) : MeasurableSet (E n) := measurableSet_le hf measurable_const
  have ha : Antitone E := by
    intro i j hij x hx
    exact hx.trans (ENNReal.coe_le_coe.mpr (pow_le_pow_right_of_le_one' (by norm_num [b]) hij))
  have he : (⋂ n, E n) =ᵐ[μ] (∅ : Set α) := by
    filter_upwards [hp] with x hx
    apply propext
    change (x ∈ ⋂ n, E n) ↔ False
    refine ⟨?_, False.elim⟩
    intro hn
    have hfb : f x ≤ 0 := ge_of_tendsto
      (show Tendsto (fun n : ℕ => ((b ^ n : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0) by
        simp only [ENNReal.coe_pow]
        exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num [b]))
      (Eventually.of_forall fun n => Set.mem_iInter.mp hn n)
    exact hx.not_ge hfb
  have hlim := tendsto_measure_iInter_atTop
    (fun n => (hE n).nullMeasurableSet) ha ⟨0, measure_ne_top μ _⟩
  rw [measure_congr he, measure_empty] at hlim
  obtain ⟨N, hN⟩ := (hlim.eventually (eventually_lt_nhds (show (0 : ℝ≥0∞) < 1 / 4 by norm_num))).exists
  refine ⟨b ^ N / 4, by positivity, ?_, ?_⟩
  · exact div_le_div_of_nonneg_right (pow_le_one₀ (show 0 ≤ b from bot_le) (by norm_num [b])) (by positivity)
  · apply lt_of_le_of_lt (measure_mono ?_) hN
    intro x hx
    change f x ≤ _ at hx
    change f x ≤ _
    apply hx.trans
    have hb : 2 * (b ^ N / 4) ≤ b ^ N := by
      have hbpos : 0 ≤ b ^ N := bot_le
      linarith
    exact_mod_cast hb

lemma exists_inverse_geometric_ratio {δ : ℝ≥0} (hδ : 0 < δ)
    {ρ : ℝ≥0∞} (hρ : ρ < 1) :
    ∃ lam : ℝ, 0 < lam ∧ ρ * ((δ ^ (-lam) : ℝ≥0) : ℝ≥0∞) < 1 := by
  have hp : ContinuousAt (fun t : ℝ => (δ, -t)) 0 :=
    ContinuousAt.prodMk (f := fun _ : ℝ => δ) (g := fun t : ℝ => -t)
      continuousAt_const continuousAt_neg
  have hc0 : ContinuousAt (fun p : ℝ≥0 × ℝ => p.1 ^ p.2) (δ, -(0 : ℝ)) :=
    NNReal.continuousAt_rpow (Or.inl hδ.ne')
  have hh0 := hc0.comp (f := fun t : ℝ => (δ, -t)) hp
  change ContinuousAt (fun t : ℝ => δ ^ (-t)) 0 at hh0
  have hc : ContinuousAt (fun t : ℝ => ρ.toNNReal * δ ^ (-t)) 0 :=
    continuousAt_const.mul hh0
  have hr : ρ.toNNReal < 1 := by
    exact_mod_cast (ENNReal.toNNReal_lt_toNNReal (ne_top_of_lt hρ) ENNReal.one_ne_top).mpr hρ
  have hh := hc.eventually (eventually_lt_nhds (show ρ.toNNReal * δ ^ (-(0 : ℝ)) < 1 by simpa using hr))
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hh
  refine ⟨ε / 2, by positivity, ?_⟩
  have hh' := he (y := ε / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]; exact half_lt_self hε)
  rw [← ENNReal.coe_toNNReal (ne_top_of_lt hρ), ← ENNReal.coe_mul]
  exact_mod_cast hh'

lemma inverse_power_le_series {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ < 1)
    {lam : ℝ} (hlam : 0 < lam) {x : ℝ≥0} (hx : 0 < x) :
    ((x ^ (-lam) : ℝ≥0) : ℝ≥0∞) ≤ ((δ ^ (-lam) : ℝ≥0) : ℝ≥0∞) +
      ∑' j : ℕ, (Set.Iio (δ ^ (j + 1))).indicator
        (fun _ : ℝ≥0 => ((δ ^ (-lam) : ℝ≥0) : ℝ≥0∞) ^ (j + 2)) x := by
  classical
  have hex : ∃ n : ℕ, δ ^ (n + 1) ≤ x := by
    obtain ⟨n, hn⟩ := ((NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hδ1).eventually
      (eventually_lt_nhds hx)).exists
    exact ⟨n, (pow_le_pow_right_of_le_one' hδ1.le (Nat.le_succ n)).trans hn.le⟩
  let n := Nat.find hex
  have hnx : δ ^ (n + 1) ≤ x := Nat.find_spec hex
  have hbound : ((x ^ (-lam) : ℝ≥0) : ℝ≥0∞) ≤ ((δ ^ (-lam) : ℝ≥0) : ℝ≥0∞) ^ (n + 1) := by
    have hh := NNReal.rpow_le_rpow_of_nonpos (pow_pos hδ _) hnx (neg_nonpos.mpr hlam.le)
    have heq : (δ ^ (n + 1)) ^ (-lam) = (δ ^ (-lam)) ^ (n + 1) := by
      rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul, mul_comm, NNReal.rpow_mul,
        NNReal.rpow_natCast]
    rw [heq] at hh
    exact_mod_cast hh
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simpa [hn] using hbound.trans (le_add_right le_rfl)
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    have hlt : x < δ ^ (j + 1) := lt_of_not_ge (Nat.find_min hex (show j < n by omega))
    have hs := ENNReal.le_tsum (f := fun k : ℕ => (Set.Iio (δ ^ (k + 1))).indicator
      (fun _ : ℝ≥0 => ((δ ^ (-lam) : ℝ≥0) : ℝ≥0∞) ^ (k + 2)) x) j
    rw [Set.indicator_of_mem (show x ∈ Set.Iio (δ ^ (j + 1)) from hlt)] at hs
    exact hbound.trans (by simpa [hj, add_assoc] using hs.trans (le_add_left le_rfl))

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_LowerClip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma inverse_moment_of_geometric_tail {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ≥0∞) (hf : Measurable f)
    (hp : ∀ᵐ x ∂μ, 0 < f x ∧ f x ≠ ∞)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ < 1) {ρ : ℝ≥0∞} (hρ : ρ < 1)
    (htail : ∀ j : ℕ, μ {x | f x < ((δ ^ (j + 1) : ℝ≥0) : ℝ≥0∞)} ≤ ρ ^ j) :
    ∃ lam : ℝ, 0 < lam ∧ (∫⁻ x, f x ^ (-lam) ∂μ) < ∞ := by
  obtain ⟨lam, hlam, hr⟩ := exists_inverse_geometric_ratio hδ hρ
  let c : ℝ≥0∞ := ((δ ^ (-lam) : ℝ≥0) : ℝ≥0∞)
  let E := fun j : ℕ => {x | f x < ((δ ^ (j + 1) : ℝ≥0) : ℝ≥0∞)}
  have hE (j : ℕ) : MeasurableSet (E j) := measurableSet_lt hf measurable_const
  have hbound : ∀ᵐ x ∂μ, f x ^ (-lam) ≤ c + ∑' j : ℕ, (E j).indicator (fun _ => c ^ (j + 2)) x := by
    filter_upwards [hp] with x hx
    have hh := inverse_power_le_series hδ hδ1 hlam (ENNReal.toNNReal_pos hx.1.ne' hx.2)
    rw [ENNReal.coe_rpow_of_ne_zero (ENNReal.toNNReal_pos hx.1.ne' hx.2).ne', ENNReal.coe_toNNReal hx.2] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    apply tsum_congr
    intro j
    simp only [Set.indicator, E, Set.mem_ofPred_eq, Set.mem_Iio]
    have heq : (f x).toNNReal < δ ^ (j + 1) ↔ f x < ((δ ^ (j + 1) : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hx.2]
    simp only [heq, c]
  have hi : (∫⁻ x, f x ^ (-lam) ∂μ) ≤ c + ∑' j : ℕ, c ^ (j + 2) * ρ ^ j := by
    apply (lintegral_mono_ae hbound).trans
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_tsum (fun j => (measurable_const.indicator (hE j)).aemeasurable)]
    refine add_le_add le_rfl ?_
    apply ENNReal.tsum_le_tsum
    intro j
    rw [lintegral_indicator (hE j), lintegral_const, Measure.restrict_apply_univ]
    exact mul_le_mul' le_rfl (htail j)
  have heq : (∑' j : ℕ, c ^ (j + 2) * ρ ^ j) = c ^ 2 * (1 - c * ρ)⁻¹ := by
    simp_rw [pow_add, mul_right_comm (c ^ _) (c ^ 2), ← mul_pow]
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, mul_comm]
  refine ⟨lam, hlam, lt_of_le_of_lt hi ?_⟩
  rw [heq]
  apply ENNReal.add_lt_top.mpr
  constructor
  · exact ENNReal.coe_lt_top
  · apply ENNReal.mul_lt_top (by simp [c])
    exact ENNReal.inv_lt_top.mpr (tsub_pos_iff_lt.mpr (by simpa [mul_comm] using hr))

def lowerClip (n : ℕ) (x : ℝ) : ℝ := max x (-(n : ℝ))

def prefixMax (z : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => max (prefixMax z n) (z n)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ClippedInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

noncomputable def clippedInverse (δ lam : ℝ) (q : ℝ≥0∞) : ℝ :=
  (max q.toReal δ) ^ (-lam)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_WordHeightGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

noncomputable def truncatedMean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (s : ℝ) : ℝ := ∫ x, min (f x) s ∂μ

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonWordIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

def realPartialSum (X : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, X k

def partialSumMax (X : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => max (partialSumMax X n) |realPartialSum X (n+1)|

noncomputable def absSlope (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SymmetricTruncate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

noncomputable def symmetricTruncate (z x : ℝ) : ℝ := if |x| ≤ z then x else 0
noncomputable def truncatedTailCost (z x : ℝ) : ℝ := if z < |x| then z^2 else 0

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RecordIndexTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma exists_integer_median (μ : Measure ℤ) [IsProbabilityMeasure μ] :
    ∃ b : ℤ, (1/2 : ℝ≥0∞) ≤ μ (Set.Iic b) ∧ (1/2 : ℝ≥0∞) ≤ μ (Set.Ici b) := by
  have hhalf : (1/2 : ℝ≥0∞) < 1 := by norm_num
  have ht : ∀ᶠ z : ℤ in atTop, (1/2 : ℝ≥0∞) < μ (Set.Iic z) :=
    (tendsto_measure_Iic_atTop μ).eventually (Ioi_mem_nhds (by simpa only [measure_univ] using hhalf))
  have hb : ∀ᶠ z : ℤ in atBot, (1/2 : ℝ≥0∞) < μ (Set.Ici z) :=
    (tendsto_measure_Ici_atBot μ).eventually (Ioi_mem_nhds (by simpa only [measure_univ] using hhalf))
  obtain ⟨b, hb⟩ := hb.exists
  have hbound : ∀ z : ℤ, (1/2 : ℝ≥0∞) ≤ μ (Set.Iic z) → b ≤ z := by
    intro z hz
    by_contra h
    have hzb : z < b := lt_of_not_ge h
    have hdis : Disjoint (Set.Iic z) (Set.Ici b) := Set.disjoint_left.mpr
      (fun x hx hx' => (not_le_of_gt hzb) (hx'.trans hx))
    have hadd : μ (Set.Iic z) + μ (Set.Ici b) ≤ 1 := by
      rw [← measure_union hdis measurableSet_Ici]
      exact prob_le_one
    have hlt : (1 : ℝ≥0∞) < μ (Set.Iic z) + μ (Set.Ici b) := by
      calc
        1 = (1/2 : ℝ≥0∞) + (1/2 : ℝ≥0∞) := (ENNReal.add_halves 1).symm
        _ < μ (Set.Iic z) + μ (Set.Ici b) := ENNReal.add_lt_add_of_le_of_lt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hz hb
    exact (not_lt_of_ge hadd) hlt
  obtain ⟨m, hm, hmin⟩ := Int.exists_least_of_bdd ⟨b,hbound⟩ (ht.exists.imp fun z hz => hz.le)
  refine ⟨m,hm,?_⟩
  have hprev : μ (Set.Iic (m-1)) < (1/2 : ℝ≥0∞) := by
    by_contra hp
    have := hmin (m-1) (le_of_not_gt hp)
    omega
  have hun : Set.Iic (m-1) ∪ Set.Ici m = Set.univ := by
    ext z
    simp only [Set.mem_union,Set.mem_Iic,Set.mem_Ici,Set.mem_univ,iff_true]
    omega
  have hdis : Disjoint (Set.Iic (m-1)) (Set.Ici m) := Set.disjoint_left.mpr (fun z hz hz' => by
    simp only [Set.mem_Iic,Set.mem_Ici] at hz hz'
    omega)
  have hadd : μ (Set.Iic (m-1)) + μ (Set.Ici m) = 1 := by
    rw [← measure_union hdis measurableSet_Ici,hun,measure_univ]
  by_contra hh
  have hm' := lt_of_not_ge hh
  have hlt := ENNReal.add_lt_add hprev hm'
  rw [hadd] at hlt
  rw [ENNReal.add_halves] at hlt
  exact (lt_irrefl _) hlt

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IntegerMedian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

noncomputable def integerMedian (μ : Measure ℤ) [IsProbabilityMeasure μ] : ℤ :=
  (exists_integer_median μ).choose

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GridOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

def GridOscillation {Ω : Type*} (X : ℕ → Ω → ℝ) (N H : ℕ) (a : ℝ) : Set Ω :=
  {ω | ∃ j ≤ N, ∃ k ≤ N, j ≤ k ∧ k ≤ j+H ∧
    a < |realPartialSum (fun l => X l ω) k-realPartialSum (fun l => X l ω) j|}

def unitRamp (t : ℝ) : ℝ := min 1 (max 0 t)

@[continuity, fun_prop] lemma continuous_unitRamp : Continuous unitRamp := by unfold unitRamp; fun_prop

noncomputable def linearPolygon (x : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, unitRamp (t-k)*x k

noncomputable instance continuousPathMeasurableSpace : MeasurableSpace C(unitInterval,ℝ) := borel _

instance continuousPathBorelSpace : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩

noncomputable def polygonPath (N : ℕ) (scale : ℝ) (x : ℕ → ℝ) : C(unitInterval,ℝ) :=
  ∑ k ∈ Finset.range N, (x k) •
    (⟨fun t => unitRamp (scale*(t:ℝ)-k),by fun_prop⟩ : C(unitInterval,ℝ))

lemma measurable_polygonPath {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) (N : ℕ) (scale : ℝ) :
    Measurable (fun ω => polygonPath N scale (fun k => X k ω)) := by
  unfold polygonPath
  fun_prop

noncomputable def scaledPolygon (x : ℕ → ℝ) (r n T : ℝ) : C(unitInterval,ℝ) :=
  r⁻¹ • polygonPath (⌊T*n⌋₊+1) (T*n) x

lemma measurable_scaledPolygon {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) (r n T : ℝ) :
    Measurable (fun ω => scaledPolygon (fun k => X k ω) r n T) := by
  exact (measurable_polygonPath X hX _ _).const_smul (r⁻¹ : ℝ)

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_OrderedTimes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

noncomputable def orderedTimes (I : Finset unitInterval) (i : Fin (I.card+1)) : unitInterval :=
  if h : i = 0 then 0 else I.orderEmbOfFin rfl (i.pred h)

noncomputable def incrementCumsum (I : Finset unitInterval) : (Fin I.card → ℝ) →L[ℝ] (I → ℝ) :=
  { toFun x i := ∑ j ≤ (I.orderIsoOfFin rfl).symm i, x j
    map_add' x y := by ext; simp [Finset.sum_add_distrib]
    map_smul' m x := by ext; simp [Finset.mul_sum]
    cont := by fun_prop }

noncomputable def gaussianPathFiniteLaw (T : ℝ) (I : Finset unitInterval) : Measure (I → ℝ) :=
  (Measure.pi (fun j : Fin I.card => gaussianReal 0
    (Real.toNNReal (T*((orderedTimes I j.succ : ℝ)-orderedTimes I j.castSucc))))).map
    (incrementCumsum I)

instance gaussianPathFiniteLaw_probability (T : ℝ) (I : Finset unitInterval) :
    IsProbabilityMeasure (gaussianPathFiniteLaw T I) := by
  unfold gaussianPathFiniteLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma continuous_path_restrict (I : Finset unitInterval) :
    Continuous (fun f : C(unitInterval,ℝ) => I.restrict f) := by
  apply continuous_pi
  intro j
  exact continuous_eval_const _

noncomputable def renewalSum (L : ℕ → ℕ) (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, L k

open scoped Classical in
noncomputable def renewalCount (L : ℕ → ℕ) (h : ℕ) : ℕ :=
  Nat.findGreatest (fun k => renewalSum L k ≤ h) h

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CommonWidthProcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

noncomputable def renewalRewardIncrement (x : ℕ → ℝ) (L : ℕ → ℕ) (h : ℕ) : ℝ :=
  realPartialSum x (renewalCount L (h+1))-realPartialSum x (renewalCount L h)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_AlignedRecordPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def FirstPairTest {α : Type*} (A : ℕ × ℕ → Set α) (q : ℕ × ℕ) : Set α :=
  A q ∩ {P | ∀ j < q.1, ∀ k < q.2, P ∉ A (j,k)}

def HeightBlockRelation (H b : ℕ) : Set (ℕ × ℕ) :=
  {sr | sr.2 ≤ H ∧ sr.1 = (sr.2/b)*b}

def HeightOscillation {Ω : Type*} (F : ℕ → Ω → ℝ) (J : Set (ℕ × ℕ)) (z : ℝ) : Set Ω :=
  {ω | ∃ s h, (s,h) ∈ J ∧ z < |F h ω-F s ω|}

def HeightGapEvent {Ω : Type*} (F B : ℕ → Ω → ℝ) (H : ℕ) (z : ℝ) : Set Ω :=
  {ω | ∃ h ≤ H, z < |F h ω-B h ω|}

end DirectionalTransience
end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CappedExp
attribute [-instance] _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def cappedExp (t : ℝ) (N : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => min (N : ℝ) (Real.exp (t*x)))
    (by fun_prop) N (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_min (Nat.cast_nonneg _) (Real.exp_pos _).le)]
      exact min_le_left _ _)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_PathPointMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def pathPointMean (G : Measure C(unitInterval,ℝ)) (t : unitInterval) : ℝ :=
  ∫ g, g t ∂G

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GridLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def GridLinear (q : ℝ) (f : C(unitInterval,ℝ)) : Prop :=
  ∀ (j : ℕ) (u v t : unitInterval), q*(u:ℝ) = j → q*(v:ℝ) = j+1 →
    (u:ℝ) ≤ t → (t:ℝ) ≤ v →
    f t = (1-(q*(t:ℝ)-j))*f u+(q*(t:ℝ)-j)*f v

noncomputable def pathRestrictScale (a : unitInterval) : C(unitInterval,ℝ) →L[ℝ] C(unitInterval,ℝ) :=
  ContinuousMap.compCLM ℝ ℝ ⟨fun t => a*t,by fun_prop⟩

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_HeightIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def heightIncrement (F : ℕ → ℝ) (k : ℕ) : ℝ := F (k+1)-F k

lemma measurable_heightIncrement {Ω : Type*} [MeasurableSpace Ω]
    (F : ℕ → Ω → ℝ) (hF : ∀ k, Measurable (F k)) (j : ℕ) :
    Measurable (fun ω => heightIncrement (fun k => F k ω) j) := (hF (j+1)).sub (hF j)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_HeightPolygon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def heightPolygon (F : ℕ → ℝ) (r n T : ℝ) : C(unitInterval,ℝ) :=
  ContinuousMap.const _ (F 0/r) + scaledPolygon (heightIncrement F) r n T

lemma measurable_heightPolygon {Ω : Type*} [MeasurableSpace Ω]
    (F : ℕ → Ω → ℝ) (hF : ∀ k, Measurable (F k)) (r n T : ℝ) :
    Measurable (fun ω => heightPolygon (fun k => F k ω) r n T) := by
  exact (ContinuousMap.continuous_const'.measurable.comp ((hF 0).div_const _)).add
    (measurable_scaledPolygon _ (measurable_heightIncrement F hF) _ _ _)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_GaussianPathFiniteLawSmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def heightPathLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → Ω → ℝ) (hF : ∀ k, Measurable (F k)) (r n T : ℝ) : ProbabilityMeasure C(unitInterval,ℝ) :=
  ⟨μ.map (fun x => heightPolygon (fun k => F k x) r n T),
    (Measure.isProbabilityMeasure_map_iff
      (measurable_heightPolygon F hF r n T).aemeasurable).2 inferInstance⟩

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_NonCollapsedSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

noncomputable def dyadicCut (j : ℕ) : ℝ := (1/2)^j

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FavorablePairFraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

noncomputable def capExcessTest (a D : ℝ) : C(unitInterval,ℝ) :=
  ⟨fun x => max ((min (D*(x:ℝ)) 1)^2-a^2) 0,by fun_prop⟩

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CappedMomentTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

noncomputable def unitTailSquare (a : ℝ) (x : unitInterval) : ℝ :=
  if a < (x:ℝ) then (x:ℝ)^2 else 0

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_SelectedFiniteKernel
attribute [-instance] _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

noncomputable def normalizeFinite {α : Type*} [MeasurableSpace α] (μ : Measure α) : Measure α :=
  (μ Set.univ)⁻¹ • μ

lemma normalizeFinite_probability {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (h0 : μ Set.univ ≠ 0) (ht : μ Set.univ ≠ ∞) : IsProbabilityMeasure (normalizeFinite μ) := by
  refine ⟨?_⟩
  simpa [normalizeFinite,Measure.smul_apply] using ENNReal.inv_mul_cancel h0 ht

lemma measurable_normalizeFinite {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (μ : Ω → Measure α) (hμ : Measurable μ) : Measurable (fun ω => normalizeFinite (μ ω)) := by
  apply Measure.measurable_of_measurable_coe
  intro U hU
  simp only [normalizeFinite,Measure.smul_apply,smul_eq_mul]
  exact (((Measure.measurable_coe MeasurableSet.univ).comp hμ).inv).mul
    ((Measure.measurable_coe hU).comp hμ)

noncomputable def selectedFiniteKernel {α : Type*} [MeasurableSpace α]
    (D : Measure α) (E : Set α) (dummy : α) (failure strict : Prop)
    [Decidable failure] [Decidable strict] : Measure α :=
  if failure then Measure.dirac dummy else normalizeFinite (if strict then D.restrict E else D)

lemma selectedFiniteKernel_measurable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (D : Ω → Measure α) (hD : Measurable D) (E : Set α) (hE : MeasurableSet E)
    (dummy : α) (failure strict : Ω → Prop) [DecidablePred failure] [DecidablePred strict]
    (hf : MeasurableSet {ω | failure ω}) (hs : MeasurableSet {ω | strict ω}) :
    Measurable (fun ω => selectedFiniteKernel (D ω) E dummy (failure ω) (strict ω)) := by
  unfold selectedFiniteKernel
  apply Measurable.ite hf measurable_const
  apply measurable_normalizeFinite
  apply Measurable.ite hs _ hD
  apply Measure.measurable_of_measurable_coe
  intro U hU
  simp only [Measure.restrict_apply hU]
  exact (Measure.measurable_coe (hU.inter hE)).comp hD

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SelectedEndpointMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

noncomputable def selectedEndpointLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N E : Set Ω) (Y : Ω → ℝ) (b : ℝ) (failure strict : Prop)
    [Decidable failure] [Decidable strict] : Measure ℝ :=
  if failure then Measure.dirac b else (μ[|if strict then E else N]).map Y

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurvePolicyPMF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def policySafe {G : Type*} [Add G] (Good : G → Prop) : G → List G → Prop
  | _, [] => True
  | x, u::w => Good x ∧ policySafe Good (x+u) w

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_MomentRescaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

noncomputable def cappedMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (L : ℝ) : ℝ := ∫ x, (min (X x) L)^2 ∂μ
noncomputable def cappedTailMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (A L : ℝ) : ℝ := ∫ x, (if A < X x then (min (X x) L)^2 else 0) ∂μ

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SuccessfulScaledTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

noncomputable def unitCap (x : ℝ) : unitInterval :=
  ⟨min (max x 0) 1,le_min (le_max_right _ _) zero_le_one,min_le_right _ _⟩

lemma continuous_unitCap : Continuous unitCap := by
  apply Continuous.subtype_mk
  exact (continuous_id.max continuous_const).min continuous_const

noncomputable def unitCapLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X) :
    ProbabilityMeasure unitInterval :=
  ⟨μ.map (unitCap ∘ X),⟨by
    rw [Measure.map_apply (continuous_unitCap.measurable.comp hX) MeasurableSet.univ,
      Set.preimage_univ,measure_univ]⟩⟩

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CurvePolicyAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def iidListPMF {G : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]
    [Countable G] (p : PMF G) (n : ℕ) : PMF (List G) :=
  ((Measure.pi fun _ : Fin n => p.toMeasure).toPMF).map List.ofFn

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IidListProcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def listCenteredMax {G : Type*} (F : G → ℝ) (c : ℝ) (w : List G) : ℝ :=
  partialSumMax (fun k => if h : k < w.length then F (w.get ⟨k,h⟩)-c else 0) w.length

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def symmetricClip (w : ℝ≥0) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun z => max (-(w:ℝ)) (min (w:ℝ) z),by fun_prop⟩ (2*w)
    (fun x y => by
      rw [Real.dist_eq]
      change |max (-(w:ℝ)) (min (w:ℝ) x)-max (-(w:ℝ)) (min (w:ℝ) y)| ≤ 2*(w:ℝ)
      apply abs_le.mpr
      have hw : -(w:ℝ) ≤ (w:ℝ) := by linarith [w.coe_nonneg]
      have hx0 := le_max_left (-(w:ℝ)) (min (w:ℝ) x)
      have hy0 := le_max_left (-(w:ℝ)) (min (w:ℝ) y)
      have hx1 : max (-(w:ℝ)) (min (w:ℝ) x) ≤ w := max_le hw (min_le_left _ _)
      have hy1 : max (-(w:ℝ)) (min (w:ℝ) y) ≤ w := max_le hw (min_le_left _ _)
      constructor <;> linarith)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def clippedBCF (F : ℝ →ᵇ ℝ) (w : ℝ≥0) : ℝ →ᵇ ℝ :=
  F.compContinuous (symmetricClip w).toContinuousMap

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FluctuationScaleUpperMultiple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma clipped_three_halves_continuous : Continuous
    (fun x : ℝ => min (|1+x|^((3:ℝ)/2)) ((2:ℝ)^((3:ℝ)/2))) := by
  exact (((continuous_const.add continuous_id).abs).rpow_const
    (fun _ => Or.inr (by norm_num))).min continuous_const

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ClippedThreeHalves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def clippedThreeHalves : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => min (|1+x|^((3:ℝ)/2)) ((2:ℝ)^((3:ℝ)/2)),clipped_three_halves_continuous⟩
    (2*((2:ℝ)^((3:ℝ)/2))) (by
      intro x y
      have hn (x : ℝ) : 0 ≤ min (|1+x|^((3:ℝ)/2)) ((2:ℝ)^((3:ℝ)/2)) :=
        le_min (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (by norm_num) _)
      change |min (|1+x|^((3:ℝ)/2)) ((2:ℝ)^((3:ℝ)/2))-
        min (|1+y|^((3:ℝ)/2)) ((2:ℝ)^((3:ℝ)/2))| ≤ _
      have hx := min_le_right (|1+x|^((3:ℝ)/2)) ((2:ℝ)^((3:ℝ)/2))
      have hy := min_le_right (|1+y|^((3:ℝ)/2)) ((2:ℝ)^((3:ℝ)/2))
      exact abs_le.mpr ⟨by linarith [hn x,hn y],by linarith [hn x,hn y]⟩)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BoundaryDecorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def pairSide {α : Type*} (b : Bool) (p : α × α) : α := if b then p.2 else p.1

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FinitePastDecorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

abbrev RealPathPair := C(unitInterval,ℝ) × C(unitInterval,ℝ)
abbrev JointPastTimes (q : ℕ) := (Fin q → unitInterval) × unitInterval × unitInterval

noncomputable def jointPastIncrementMap {q : ℕ} (b : Bool) :
    C(RealPathPair × JointPastTimes q, (Fin q → ℝ × ℝ) × ℝ) where
  toFun z := ((fun a => (z.1.1 (z.2.1 a), z.1.2 (z.2.1 a))),
    if b then z.1.2 z.2.2.2 - z.1.2 z.2.2.1 else z.1.1 z.2.2.2 - z.1.1 z.2.2.1)
  continuous_toFun := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro a
      exact (continuous_eval.comp (continuous_fst.fst.prodMk (continuous_apply a |>.comp continuous_snd.fst))).prodMk
        (continuous_eval.comp (continuous_fst.snd.prodMk (continuous_apply a |>.comp continuous_snd.fst)))
    · cases b <;> simp only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
      · exact (continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd.snd.snd)).sub
          (continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd.snd.fst))
      · exact (continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd.snd.snd)).sub
          (continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd.snd.fst))

noncomputable def jointPastProductTest {q : ℕ} (F : (Fin q → ℝ × ℝ) →ᵇ ℝ)
    (G : ℝ →ᵇ ℝ) (c : ℝ) : ((Fin q → ℝ × ℝ) × ℝ) →ᵇ ℝ :=
  (F.compContinuous ⟨Prod.fst,continuous_fst⟩) *
    ((G.compContinuous ⟨Prod.snd,continuous_snd⟩)-BoundedContinuousFunction.const _ c)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_ContinuousCrossPast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def jointPastGapMap {q : ℕ} : C(RealPathPair × JointPastTimes q,ℝ) where
  toFun z := z.1.1 z.2.2.1-z.1.2 z.2.2.1
  continuous_toFun := (continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd.snd.fst)).sub
    (continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd.snd.fst))

noncomputable def jointCrossPastTest {q : ℕ} (F : (Fin q → ℝ × ℝ) →ᵇ ℝ)
    (G g : ℝ →ᵇ ℝ) : (RealPathPair × JointPastTimes q) →ᵇ ℝ :=
  ((jointPastProductTest F G 0).compContinuous (jointPastIncrementMap false))*
  (G.compContinuous ⟨fun z => (jointPastIncrementMap true z).2,
    continuous_snd.comp (jointPastIncrementMap true).continuous⟩)*
  (g.compContinuous jointPastGapMap)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ClippedAbsThreeHalves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def clippedAbsThreeHalves : ℝ →ᵇ ℝ :=
  clippedThreeHalves.compContinuous ⟨fun x => x-1,continuous_id.sub continuous_const⟩

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction

end
end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_GridOccupation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def layerGridPoint (a : ℝ) (j : ℕ) : unitInterval :=
  Set.projIcc 0 1 (by norm_num) ((j:ℝ)/a)

noncomputable def layerGap (P : RealPathPair) (t : unitInterval) : ℝ := P.2 t-P.1 t

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def interiorPastGrid {q : ℕ} (a : ℝ) (v : Fin q → unitInterval)
    (s t : unitInterval) : JointPastTimes q :=
  ((fun z => layerGridPoint a ⌊(v z:ℝ)*a⌋₊),
    layerGridPoint a (⌊(s:ℝ)*a⌋₊+1),
    layerGridPoint a ((⌊(s:ℝ)*a⌋₊+1)+⌊((t:ℝ)-s)*a⌋₊))

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ObservedPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

noncomputable def observedPotential (b R z : ℝ) : ℝ :=
  min ((max |z| b)^((3:ℝ)/2)) ((2*R)^((3:ℝ)/2))

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RestartLyapunov
attribute [-instance] _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

def observerRewardSum {Ω : Type*} (next : Ω → Ω) (reward : Ω → ℝ≥0∞) : ℕ → Ω → ℝ≥0∞
  | 0, _ => 0
  | N+1, ω => reward ω+observerRewardSum next reward N (next ω)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_OccupationAlgebra
attribute [-instance] _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

noncomputable def occupationCoefficient (J C q M b r ρ A δ : ℝ) : ℝ :=
  C*J*(b/r)^((1:ℝ)/4)/(q*((2:ℝ)^((3:ℝ)/2)-1)) +
  M*J*(2*ρ)^((1:ℝ)/4) + M*J*A^((1:ℝ)/4)*δ

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_AllLayerOccupation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

noncomputable def occupationMacroConstant (A : ℝ) : ℝ :=
  max ((2:ℝ)^((7:ℝ)/4)) (A^2)*(2*A)^((3:ℝ)/2)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ConditionalLawTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def normalThirdMoment : ℝ := ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_JointPastMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def pairPastCoordinates {q : ℕ} (v : Fin q → unitInterval) :
    C(RealPathPair,Fin q → ℝ × ℝ) :=
  ⟨fun P z => (P.1 (v z),P.2 (v z)),by fun_prop⟩

noncomputable def pairPathIncrement (b : Bool) (s t : unitInterval) : C(RealPathPair,ℝ) :=
  ⟨fun P => if b then P.2 t-P.2 s else P.1 t-P.1 s,by cases b <;> simp <;> fun_prop⟩

def NormalJointPast (μ : Measure RealPathPair) (c : ℝ≥0) : Prop :=
  ∀ (q : ℕ) (v : Fin q → unitInterval) (s t : unitInterval),
    (∀ z, v z ≤ s) → s < t → (t:ℝ) < 1 → ∀ b : Bool,
    μ.map (fun P => (pairPastCoordinates v P,pairPathIncrement b s t P)) =
      (μ.map (pairPastCoordinates v)).prod (gaussianReal 0 (c*Real.toNNReal ((t:ℝ)-s)))

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SharedLimitNormalPast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def gridOccupationMass (μ : Measure RealPathPair) (a ρ : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (⌊a⌋₊+1), μ.real {P | |layerGap P (layerGridPoint a j)| ≤ ρ})/a

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_PastCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def nearDiagonalCutoff (ρ : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun z => max 0 (min 1 (2-|z|/ρ)),by fun_prop⟩ 2
    (fun x y => by
      rw [Real.dist_eq]
      change |max 0 (min 1 (2-|x|/ρ))-max 0 (min 1 (2-|y|/ρ))| ≤ 2
      have hx0 : 0 ≤ max 0 (min 1 (2-|x|/ρ)) := le_max_left _ _
      have hy0 : 0 ≤ max 0 (min 1 (2-|y|/ρ)) := le_max_left _ _
      have hx1 : max 0 (min 1 (2-|x|/ρ)) ≤ 1 := max_le (by norm_num) (min_le_left _ _)
      have hy1 : max 0 (min 1 (2-|y|/ρ)) ≤ 1 := max_le (by norm_num) (min_le_left _ _)
      exact abs_le.mpr ⟨by linarith,by linarith⟩)

lemma nearDiagonalCutoff_unit (ρ z : ℝ) : 0 ≤ nearDiagonalCutoff ρ z ∧ nearDiagonalCutoff ρ z ≤ 1 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

noncomputable def farDiagonalCutoff (ρ : ℝ) : ℝ →ᵇ ℝ := .const ℝ 1-nearDiagonalCutoff ρ

noncomputable def currentGapTest {q : ℕ} (g : ℝ →ᵇ ℝ) : (Fin (q+1) → ℝ × ℝ) →ᵇ ℝ :=
  g.compContinuous ⟨fun z => (z 0).1-(z 0).2,by fun_prop⟩

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_UniformRiemannMesh
attribute [-instance] _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory Filter
open scoped BigOperators Topology
namespace DirectionalTransience

noncomputable def realMesh (s t : ℝ) (n j : ℕ) : ℝ := s+(j:ℝ)*(t-s)/n

end DirectionalTransience

end

section

open MeasureTheory Filter
open scoped BigOperators Topology
namespace DirectionalTransience

noncomputable def unitMesh (s t : unitInterval) (n j : ℕ) : unitInterval :=
  Set.projIcc 0 1 zero_le_one (realMesh s t n j)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_CutoffTimeAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def cutoffMean (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (ρ : ℝ) :
    C(unitInterval,ℝ) where
  toFun s := ∫ P, nearDiagonalCutoff ρ (P.1 s-P.2 s) ∂μ
  continuous_toFun := by
    apply continuous_of_dominated (bound := fun _ => 1)
    · intro s; exact (by fun_prop : Measurable (fun P : RealPathPair => nearDiagonalCutoff ρ (P.1 s-P.2 s))).aestronglyMeasurable
    · intro s; filter_upwards [] with P
      rw [Real.norm_eq_abs,abs_of_nonneg (nearDiagonalCutoff_unit ρ _).1]
      exact (nearDiagonalCutoff_unit ρ _).2
    · exact integrable_const 1
    · filter_upwards [] with P
      fun_prop

noncomputable def cutoffMeanExtension (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (ρ : ℝ) : ℝ → ℝ :=
  fun s => cutoffMean μ ρ (Set.projIcc 0 1 zero_le_one s)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_NearCrossEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

def SeparatedCrossBound (μ : Measure RealPathPair) (A K : ℝ) : Prop :=
  ∀ (q : ℕ) (v : Fin q → unitInterval) (s t : unitInterval),
    (∀ z, v z ≤ s) → s < t → (t:ℝ) < 1 →
    ∀ (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (g : ℝ →ᵇ ℝ), UniformContinuous g →
      (∀ z, |g z| ≤ 1) → ∀ ρ : ℝ, 0 < ρ → (∀ z, |z| ≤ ρ → g z=0) →
    |∫ P, F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*
      (symmetricClip 1 (pairPathIncrement false s t P)*symmetricClip 1 (pairPathIncrement true s t P)) ∂μ| ≤
      ‖F‖*(K*Real.exp (-A*ρ^2/((t:ℝ)-s)))

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CharacteristicTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

noncomputable def charPhase (x : ℝ) : ℂ := Complex.exp ((x:ℂ)*Complex.I)

lemma charPhase_norm (x : ℝ) : ‖charPhase x‖=1 := Complex.norm_exp_ofReal_mul_I x

noncomputable def charTaylorConstant : ℝ := Real.exp 1+4

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_NormalLinearPast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def pairLinearIncrement (a b : ℝ) (s t : unitInterval) : C(RealPathPair,ℝ) :=
  ⟨fun P => a*pairPathIncrement false s t P+b*pairPathIncrement true s t P,by fun_prop⟩

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_PastPhaseExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma charPhase_continuous : Continuous charPhase := by unfold charPhase; fun_prop

noncomputable def phaseAugmentedTimes {q : ℕ} (v : Fin q → unitInterval) (s u : unitInterval) :
    Fin (q+2) → unitInterval := Fin.cons u (Fin.cons s v)

noncomputable def phaseAugmentedTest {q : ℕ} (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ) :
    (Fin (q+2) → ℝ × ℝ) →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun z => F (fun i => z i.succ.succ)*
      charPhase (a*((z 0).1-(z 1).1)+b*((z 0).2-(z 1).2)),by
        apply Continuous.mul (F.continuous.comp (by fun_prop))
        exact charPhase_continuous.comp (by fun_prop)⟩ (2*‖F‖) (by
      intro x y
      calc
        _ ≤ ‖F (fun i => x i.succ.succ)*charPhase (a*((x 0).1-(x 1).1)+b*((x 0).2-(x 1).2))‖+
          ‖F (fun i => y i.succ.succ)*charPhase (a*((y 0).1-(y 1).1)+b*((y 0).2-(y 1).2))‖ := by rw [dist_eq_norm]; exact norm_sub_le _ _
        _ ≤ _ := by
          rw [norm_mul,norm_mul,charPhase_norm,charPhase_norm,mul_one,mul_one]
          nlinarith only [F.norm_coe_le_norm (fun i => x i.succ.succ),F.norm_coe_le_norm (fun i => y i.succ.succ)])

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def jointTaylorCoeff (a b : ℝ) : ℝ :=
  8*charTaylorConstant*(|a|+|b|)^3*normalThirdMoment+8*|a*b| *normalThirdMoment

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CharacteristicProductLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def linearPhaseTest {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) : E →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => charPhase (L x),
    charPhase_continuous.comp L.continuous⟩ 2 (by
      intro x y
      rw [dist_eq_norm]
      calc
        _ ≤ ‖charPhase (L x)‖+‖charPhase (L y)‖ := norm_sub_le _ _
        _ = 2 := by rw [charPhase_norm,charPhase_norm]; norm_num)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

def FullNormalJointPast (μ : Measure RealPathPair) (c : ℝ≥0) : Prop :=
  ∀ (q : ℕ) (v : Fin q → unitInterval) (s t : unitInterval),
    (∀ z, v z ≤ s) → s < t → (t:ℝ) < 1 →
    μ.map (fun P => (pairPastCoordinates v P,(pairPathIncrement false s t P,pairPathIncrement true s t P))) =
      (μ.map (pairPastCoordinates v)).prod
        ((gaussianReal 0 (c*Real.toNNReal ((t:ℝ)-s))).prod
         (gaussianReal 0 (c*Real.toNNReal ((t:ℝ)-s))))

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ProductNormalJointPast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def pathPastCoordinates {q : ℕ} (v : Fin q → unitInterval) :
    C(C(unitInterval,ℝ),Fin q → ℝ) := ⟨fun P z => P (v z),by fun_prop⟩

noncomputable def pathIncrement (s t : unitInterval) : C(C(unitInterval,ℝ),ℝ) :=
  ⟨fun P => P t-P s,by fun_prop⟩

def NormalSinglePast (μ : Measure C(unitInterval,ℝ)) (c : ℝ≥0) : Prop :=
  ∀ (q : ℕ) (v : Fin q → unitInterval) (s t : unitInterval),
    (∀ z, v z ≤ s) → s < t → (t:ℝ) < 1 →
    μ.map (fun P => (pathPastCoordinates v P,pathIncrement s t P)) =
      (μ.map (pathPastCoordinates v)).prod (gaussianReal 0 (c*Real.toNNReal ((t:ℝ)-s)))

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def pairRestricted (I : Finset unitInterval) : C(RealPathPair,I → ℝ × ℝ) :=
  ⟨fun P z => (P.1 z,P.2 z),by fun_prop⟩

noncomputable def pairIncrement (s t : unitInterval) : C(RealPathPair,ℝ × ℝ) :=
  ⟨fun P => (P.1 t-P.1 s,P.2 t-P.2 s),by fun_prop⟩

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def pairExtend (I : Finset unitInterval) (t s : unitInterval) (hs : s ∈ I) :
    ((I → ℝ × ℝ) × (ℝ × ℝ)) → (↑(insert t I) → ℝ × ℝ) :=
  fun z j => if h : j.val=t then z.1 ⟨s,hs⟩+z.2 else
    z.1 ⟨j,Finset.mem_of_mem_insert_of_ne j.property h⟩

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_InteriorPairMeasureExt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def shrinkTime (n : ℕ) (t : unitInterval) : unitInterval :=
  ⟨((n:ℝ)+1)/((n:ℝ)+2)*(t:ℝ),by
    have hn : 0 ≤ ((n:ℝ)+1)/((n:ℝ)+2) := by positivity
    have hle : ((n:ℝ)+1)/((n:ℝ)+2) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    exact ⟨mul_nonneg hn t.property.1,(mul_le_mul_of_nonneg_left t.property.2 hn).trans (by simpa using hle)⟩⟩

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_HeightTubeWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace DirectionalTransience

def heightTubeEndpointEvent (Y : ℕ → ℝ) (H : ℕ) (L R : ℝ) : Prop :=
  (∀ j ≤ H, |Y j| ≤ L) ∧ |Y H| ≤ R

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_PathWindowTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace DirectionalTransience

def pathWindowEvent (τ : unitInterval) (δ ρ B : ℝ) : Set C(unitInterval,ℝ) :=
  {g | Set.MapsTo g (Metric.closedBall τ δ) (Set.Ioo (-ρ) ρ) ∧ ‖g‖ < B}

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SmallScaleGaussianMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

noncomputable def bandTruncate (z R x : ℝ) : ℝ := symmetricTruncate R x-symmetricTruncate z x

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RelativeBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience
namespace TupleKernel

noncomputable def dependentPair {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (K : A → Measure B) : Measure (A × B) :=
  μ.bind (fun a => (K a).map (fun b => (a,b)))

end TupleKernel

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_SeedMedian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def IsIntegerMedian (μ : Measure ℤ) (b : ℤ) : Prop :=
  (1/2:ℝ≥0∞) ≤ μ (Set.Iic b) ∧ (1/2:ℝ≥0∞) ≤ μ (Set.Ici b)

lemma exists_nat_integerMedian (μ : ProbabilityMeasure ℤ) :
    ∃ n : ℕ, IsIntegerMedian μ.toMeasure (Encodable.decode (α:=ℤ) n |>.getD 0) := by
  obtain ⟨b,hb⟩ := exists_integer_median μ.toMeasure
  refine ⟨Encodable.encode b, ?_⟩
  rw [Encodable.encodek]
  exact hb

noncomputable def selectedIntegerMedian (μ : ProbabilityMeasure ℤ) : ℤ :=
  (Encodable.decode (α:=ℤ) (Nat.find (exists_nat_integerMedian μ))).getD 0

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Coupling_SeedIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def seedHeight (a : ℤ) (H : ℕ) : ℕ → ℤ
  | 0 => a
  | n+1 => seedHeight a H n+H

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_TailCuts
attribute [-instance] _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Filter
open scoped Topology ENNReal
namespace TailCuts

def score (L U : ℤ → ℝ) (R j : ℤ) : ℝ := min (L j) (U (j + R))

end TailCuts

namespace TailCuts

noncomputable def lower (μ : Measure ℤ) (j : ℤ) : ℝ := μ.real (Set.Iic j)
noncomputable def upper (μ : Measure ℤ) (j : ℤ) : ℝ := μ.real (Set.Ici j)

end TailCuts

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_CanonicalLogExcess
attribute [-instance] _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def canonicalLogExcess {Ω : Type*} (A : ℝ) (p : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  (⨆ n : ℕ, ENNReal.ofReal (-Real.log (p n ω)-2*A*Real.log ((n:ℝ)+2))).toReal

noncomputable def finiteLogExcess {Ω : Type*} (A : ℝ) (p : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  (⨆ n : Fin (N+1), ENNReal.ofReal (-Real.log (p n ω)-2*A*Real.log ((n:ℝ)+2))).toReal

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayTopology
attribute [-instance] _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace DirectionalTransience.StationaryCompact

instance discreteOnePoint_countable (H : Type*) [Countable H] : Countable (OnePoint H) := by
  unfold OnePoint
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance discreteOnePoint_firstCountable (H : Type*) [TopologicalSpace H]
    [DiscreteTopology H] [Countable H] : FirstCountableTopology (OnePoint H) := by
  constructor
  intro x
  induction x using OnePoint.rec with
  | coe x =>
    rw [OnePoint.nhds_coe_eq, nhds_discrete]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  | infty =>
    rw [OnePoint.nhds_infty_eq, coclosedCompact_eq_cocompact, cocompact_eq_cofinite]
    have : (cofinite : Filter H).IsCountablyGenerated :=
      (show (cofinite : Filter H).HasCountableBasis Set.Finite (fun s => sᶜ) from
        ⟨Filter.hasBasis_cofinite, Set.Countable.ofPred_finite⟩).isCountablyGenerated
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance discreteOnePoint_secondCountable (H : Type*) [TopologicalSpace H]
    [DiscreteTopology H] [Countable H] : SecondCountableTopology (OnePoint H) := inferInstance

end DirectionalTransience.StationaryCompact

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_Array
attribute [-instance] _root_.OAI.DirectionalTransience.annealedLaw_probability _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.environmentLaw_probability _root_.OAI.DirectionalTransience.initialLaw_probability _root_.OAI.DirectionalTransience.state_measurableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped NNReal ENNReal BigOperators Classical
namespace DirectionalTransience

instance row_compact (d : ℕ) : CompactSpace (Row d) := by
  apply isCompact_iff_compactSpace.mp
  have hbox : IsCompact {p : Direction d → ℝ≥0 | ∀ e, p e∈Set.Icc 0 1} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  apply hbox.of_isClosed_subset (isClosed_eq (by fun_prop) continuous_const)
  intro p hp e
  exact ⟨bot_le, (Finset.single_le_sum (fun j _ => bot_le) (Finset.mem_univ e)).trans_eq hp⟩

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_StoppedSplice
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma independent_diagonal_lintegral {Ω A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → A) (V : Ω → B) (hU : Measurable U) (hV : Measurable V)
    (hind : IndepFun U V μ) (F : A × B → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, F (U ω,V ω) ∂μ) = ∫⁻ η, ∫⁻ ξ, F (U η,V ξ) ∂μ ∂μ := by
  rw [←lintegral_map hF (hU.prodMk hV),
    hind.map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable,
    lintegral_prod _ hF.aemeasurable]
  have hm : Measurable (fun a => ∫⁻ b, F (a,b) ∂μ.map V) :=
    Measurable.lintegral_prod_right (f:=fun a b => F (a,b)) hF
  rw [lintegral_map hm hU]
  apply lintegral_congr
  intro η
  exact lintegral_map (hF.comp measurable_prodMk_left) hV

noncomputable def rowGraft {d : ℕ} (S : Set (Lattice d))
    (η ξ : Environment d) : Environment d := fun x => if x∈S then η x else ξ x

lemma rowGraft_diagonal {d : ℕ} (S : Set (Lattice d)) (ω : Environment d) :
    rowGraft S ω ω=ω := by ext x; simp [rowGraft]

noncomputable def stoppedRowGraft {d : ℕ} (S : ℕ → Set (Lattice d))
    (τ : Environment d → ℕ) (η ξ : Environment d) : Environment d :=
  rowGraft (S (τ η)) η ξ

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_StoppedWindowEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace DirectionalTransience.StoppedWindow

variable {A B Z : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace Z] [StandardBorelSpace B] [Nonempty B]

theorem fresh_prod_chain (Q : Measure (A × B)) [IsFiniteMeasure Q]
    (Pdata : Measure A) [IsFiniteMeasure Pdata]
    (Pfield : Measure B) [IsProbabilityMeasure Pfield] :
    klDiv Q (Pdata.prod Pfield) =
      klDiv Q.fst Pdata + klDiv Q (Q.fst.prod Pfield) := by
  have h := klDiv_compProd_eq_add Q.fst Pdata Q.condKernel (Kernel.const A Pfield)
  simpa only [Measure.disintegrate, Measure.compProd_const] using h

omit [StandardBorelSpace B] [Nonempty B] in
theorem same_auxiliary_cost (Q P : Measure A) [IsFiniteMeasure Q] [IsFiniteMeasure P]
    (R : Measure B) [IsProbabilityMeasure R] :
    klDiv (Q.prod R) (P.prod R) = klDiv Q P := by
  simpa only [Measure.compProd_const] using klDiv_compProd_left Q P (Kernel.const A R)

end DirectionalTransience.StoppedWindow

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_DominatedEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace DirectionalTransience.StoppedWindow
variable {X A B F G : Type*} [MeasurableSpace X] [MeasurableSpace A]
  [MeasurableSpace B] [MeasurableSpace F] [MeasurableSpace G]

lemma sample_data_map (μ : Measure X) [IsFiniteMeasure μ]
    (g : X → A) (hg : Measurable g) (f : X → F) (hf : Measurable f)
    (K : Kernel A B) [IsMarkovKernel K] :
    (μ.compProd (K.comap g hg)).map (fun p => ((g p.1,p.2),f p.1)) =
      (((Kernel.id.prod K) ∥ₖ Kernel.id) ∘ₘ (μ.map (fun x => (g x,f x)))) := by
  apply Measure.ext_of_lintegral
  intro h hh
  have hw : Measurable (fun p : X × B => ((g p.1,p.2),f p.1)) :=
    ((hg.comp measurable_fst).prodMk measurable_snd).prodMk (hf.comp measurable_fst)
  have hk : Measurable (fun z : A × F => ∫⁻ y, h y ∂((Kernel.id.prod K) ∥ₖ Kernel.id) z) :=
    hh.lintegral_kernel
  rw [lintegral_map hh hw,Measure.lintegral_compProd (show Measurable (fun p : X × B => h ((g p.1,p.2),f p.1)) from hh.comp hw),
    Measure.lintegral_bind (Kernel.aemeasurable _) hh.aemeasurable,
    lintegral_map hk (hg.prodMk hf)]
  apply lintegral_congr
  intro x
  rw [Kernel.lintegral_parallelComp _ hh]
  simp_rw [Kernel.id_apply]
  simp only [Kernel.comap_apply]
  have he (p : A × B) : (∫⁻ z : F, h (p,z) ∂Measure.dirac (f x))=h (p,f x) :=
    lintegral_dirac' _ (hh.comp measurable_prodMk_left)
  simp_rw [he]
  simpa only [Kernel.id,id_eq,Function.comp_def] using (Kernel.lintegral_deterministic_prod
    (f:=id) measurable_id K (g x) (hh.comp measurable_prodMk_right)).symm

noncomputable def selectedKernel (K : Kernel A B) (u : B × F → G)
    (_ : Measurable u) : Kernel (A × F) ((A × B) × G) :=
  (((Kernel.id.prod K) ∥ₖ Kernel.id)).map (fun p => (p.1,u (p.1.2,p.2)))
instance selectedKernel_markov (K : Kernel A B) [IsMarkovKernel K]
    (u : B × F → G) (hu : Measurable u) : IsMarkovKernel (selectedKernel K u hu) := by
  unfold selectedKernel
  apply Kernel.IsMarkovKernel.map
  exact measurable_fst.prodMk (hu.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

lemma selectedKernel_lintegral (K : Kernel A B) [IsMarkovKernel K]
    (u : B × F → G) (hu : Measurable u) (h : (A × B) × G → ℝ≥0∞)
    (hh : Measurable h) (a : A) (f : F) :
    (∫⁻ q, h q ∂selectedKernel K u hu (a,f)) = ∫⁻ b, h ((a,b),u (b,f)) ∂K a := by
  have hp : Measurable (fun p : (A × B) × F => (p.1,u (p.1.2,p.2))) :=
    measurable_fst.prodMk (hu.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  rw [selectedKernel,Kernel.map_apply _ hp,lintegral_map hh hp,
    Kernel.lintegral_parallelComp _ (show Measurable (fun p : (A × B) × F => h (p.1,u (p.1.2,p.2))) from hh.comp hp)]
  simp_rw [Kernel.id_apply]
  have he (p : A × B) : (∫⁻ z : F, h (p,u (p.2,z)) ∂Measure.dirac f)=h (p,u (p.2,f)) :=
    lintegral_dirac' _ (hh.comp (measurable_const.prodMk
      (hu.comp (measurable_const.prodMk measurable_id))))
  simp_rw [he]
  exact Kernel.lintegral_deterministic_prod measurable_id K a
    (hh.comp (measurable_id.prodMk (hu.comp (measurable_snd.prodMk measurable_const))))

lemma selected_reference (δ : Measure A) [IsFiniteMeasure δ]
    (R : Kernel A F) [IsMarkovKernel R] (K : Kernel A B) [IsMarkovKernel K]
    (P : Measure G) [IsProbabilityMeasure P] (u : B × F → G) (hu : Measurable u)
    (hP : ∀ a b, (R a).map (fun f => u (b,f))=P) :
    selectedKernel K u hu ∘ₘ δ.compProd R=(δ.compProd K).prod P := by
  apply Measure.ext_of_lintegral
  intro h hh
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hh.aemeasurable,
    Measure.lintegral_compProd hh.lintegral_kernel,
    lintegral_prod _ hh.aemeasurable,
    Measure.lintegral_compProd hh.lintegral_prod_right']
  apply lintegral_congr
  intro a
  simp_rw [selectedKernel_lintegral K u hu h hh]
  have hm : Measurable (fun p : F × B => h ((a,p.2),u (p.2,p.1))) :=
    hh.comp ((measurable_const.prodMk measurable_snd).prodMk (hu.comp measurable_swap))
  rw [←lintegral_prod _ hm.aemeasurable,lintegral_prod_symm _ hm.aemeasurable]
  apply lintegral_congr
  intro b
  rw [←hP a b]
  exact (lintegral_map (show Measurable (fun y : G => h ((a,b),y)) from hh.comp measurable_prodMk_left)
    (show Measurable (fun f : F => u (b,f)) from hu.comp measurable_prodMk_left)).symm

lemma selected_kl_finite [StandardBorelSpace G] [Nonempty G]
    (Q : Measure (A × F)) [IsProbabilityMeasure Q]
    (δ : Measure A) [IsProbabilityMeasure δ]
    (R : Kernel A F) [IsMarkovKernel R] (K : Kernel A B) [IsMarkovKernel K]
    (P : Measure G) [IsProbabilityMeasure P] (u : B × F → G) (hu : Measurable u)
    (hP : ∀ a b, (R a).map (fun f => u (b,f))=P)
    (hkl : klDiv Q (δ.compProd R)≠∞) :
    let W := selectedKernel K u hu ∘ₘ Q
    klDiv W (W.fst.prod P)≠∞ := by
  have h := klDiv_comp_right_le Q (δ.compProd R) (selectedKernel K u hu)
  rw [selected_reference δ R K P u hu hP] at h
  have hf := ne_top_of_le_ne_top hkl h
  rw [fresh_prod_chain] at hf
  exact (ENNReal.add_ne_top.mp hf).2

end DirectionalTransience.StoppedWindow

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_AdaptiveFailureWeights
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def successes {Ω : Type*} (B : ℕ → Set Ω) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, if ω ∈ B k then (1:ℝ) else 0
noncomputable def failureWeight {Ω : Type*} (B : ℕ → Set Ω) (s : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (s/4*(n:ℝ)-successes B n ω)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def failureSeries {Ω : Type*} (B : ℕ → Set Ω) (s : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (failureWeight B s n ω)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BoundedAnchorAverage
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators
namespace DirectionalTransience

noncomputable def sampleAverage {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (n:ℝ)⁻¹*∑ a∈Finset.range n, X a ω

lemma sampleAverage_memLp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ a, Measurable (X a))
    (hB : ∀ a ω, |X a ω|≤1) (n : ℕ) : MemLp (sampleAverage X n) 2 μ := by
  apply MemLp.of_bound (by unfold sampleAverage; fun_prop) 1
  filter_upwards [] with ω
  dsimp only [sampleAverage]
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
  have hs : ‖∑ a∈Finset.range n, X a ω‖ ≤ (n:ℝ) := by
    calc _ ≤ ∑ a∈Finset.range n, ‖X a ω‖ := norm_sum_le _ _
         _ ≤ ∑ _a∈Finset.range n, (1:ℝ) := Finset.sum_le_sum fun a _ => hB a ω
         _ = _ := by simp
  apply (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg n))).trans
  by_cases hn : n=0
  · simp [hn]
  · simp [hn]

lemma sampleAverage_variance_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ a, Measurable (X a)) (hB : ∀ a ω, |X a ω|≤1)
    (hi : iIndepFun X μ) (n : ℕ) (hn : 0<n) :
    variance (sampleAverage X n) μ ≤ (n:ℝ)⁻¹ := by
  have hM (a : ℕ) : MemLp (X a) 2 μ :=
    MemLp.of_bound (hX a).aestronglyMeasurable 1 (Eventually.of_forall (hB a))
  have hv (a : ℕ) : variance (X a) μ ≤ 1 := by
    apply (variance_le_expectation_sq (hX a).aestronglyMeasurable).trans
    calc _ ≤ ∫ _ω, (1:ℝ) ∂μ := by
           apply integral_mono (hM a).integrable_sq (integrable_const _)
           intro ω
           dsimp
           nlinarith [hB a ω,neg_le_abs (X a ω),le_abs_self (X a ω)]
         _ = 1 := by simp
  unfold sampleAverage
  rw [variance_const_mul]
  have he : (fun ω => ∑ a∈Finset.range n, X a ω)=∑ a∈Finset.range n, X a := by
    ext ω; simp
  rw [he,IndepFun.variance_sum (fun a _ => hM a) (fun a _ b _ h => hi.indepFun h)]
  calc
    _ ≤ (n:ℝ)⁻¹^2*∑ _a∈Finset.range n, (1:ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hv a) (sq_nonneg _)
    _ = (n:ℝ)⁻¹ := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
      field_simp

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BufferChildNode
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def bufferNextRadius (R₀ r ε α : ℝ) (b : Bool) : ℝ :=
  max R₀ ((if b then 1+α else 1-ε)*r)

noncomputable def bufferRestoreLength (R₀ r ε α : ℝ) (b : Bool) : ℕ :=
  ⌈max 0 (R₀-((if b then 1+α else 1-ε)*r))⌉₊

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CappedLoss
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
namespace DirectionalTransience

noncomputable def cappedLogLoss (a q : ℝ) : ℝ :=
  if q=0 then a else min a (-Real.log q)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ProtectionLoss
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

def protectionHeight (base : ℝ) (H : ℕ → ℕ) : ℕ → ℝ
  | 0 => base
  | n+1 => protectionHeight base H n + H n

def protectionGap (G : ℝ) (r : ℕ → ℝ) : ℕ → ℝ
  | 0 => G
  | n+1 => protectionGap G r n-r n

lemma protectionHeight_mono (base : ℝ) (H : ℕ → ℕ) : Monotone (protectionHeight base H) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_add_of_nonneg_right (Nat.cast_nonneg _)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CellAttempt
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

def failedOpportunityBlocks {Ω : Type*} (F : ℕ → ℕ → Set Ω) (i : ℕ) : List ℕ → Set Ω
  | [] => Set.univ
  | n::ns => F i n ∩ failedOpportunityBlocks F (i+n) ns

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RadixBudget
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

noncomputable def lateBudget (c ρ : ℝ) (s n : ℕ) : ℝ := (c/16)*ρ/(2:ℝ)^(s+n)

lemma lateBudget_pos {c ρ : ℝ} (hc : 0 < c) (hρ : 0<ρ) (s n : ℕ) : 0<lateBudget c ρ s n := by
  unfold lateBudget; positivity

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ProtectionFirstFailure
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

def firstProtectionFailure {Ω : Type*} (q : ℕ → Ω → ℝ) (kA s : ℝ) (n : ℕ) : Set Ω :=
  {ω | (∀ j<n, Real.exp (-kA*(s+j+1))≤∏ i∈Finset.range (j+1), q i ω) ∧
    (∏ i∈Finset.range (n+1), q i ω)<Real.exp (-kA*(s+n+1))}

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CellFailure
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

def consumedCellFailure {Ω : Type*} (seed : Ω → ℝ≥0∞) (early : Ω → ℝ)
    (q : ℕ → Ω → ℝ) (g₀ g₁ kA : ℝ) (s m n : ℕ) : Set Ω :=
  {ω | n=1 ∧ seed ω < ENNReal.ofReal g₀} ∪
  {ω | n=min s m ∧ ENNReal.ofReal g₀ ≤ seed ω ∧ early ω < g₁} ∪
  {ω | s  <  n ∧ n  ≤  m ∧ ENNReal.ofReal g₀ ≤ seed ω ∧ g₁ ≤ early ω ∧
    ω∈firstProtectionFailure q kA s (n-s-1)}

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CellSchedule
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators
namespace DirectionalTransience

def cellWidth (w m i : ℕ) : ℕ := 16^(m-i)*w

def cellOpportunity (v w m i : ℕ) : ℕ :=
  if i < m then v-2*cellWidth w m i else v+w

lemma cellWidth_antitone (w m : ℕ) : Antitone (cellWidth w m) := by
  intro i j hij
  apply Nat.mul_le_mul_right
  exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le_sub_left hij m)
lemma cellOpportunity_le_end (v w m i : ℕ) : cellOpportunity v w m i ≤ v+w := by
  unfold cellOpportunity
  split
  · omega
  · rfl

def cellEarlyHeight (v w m i s : ℕ) : ℕ :=
  cellOpportunity v w m (i+min s (m-i))-(cellOpportunity v w m i+cellWidth w m i)

def cellLateHeight (v w m i s j : ℕ) : ℕ :=
  if i+s+j < m then
    cellOpportunity v w m (i+s+j+1)-cellOpportunity v w m (i+s+j) else 0

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CellExhaustion
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

def cellAttemptSuccess {Ω : Type*} (seed : Ω → ℝ≥0∞) (early : Ω → ℝ)
    (q : ℕ → Ω → ℝ) (g₀ g₁ kA : ℝ) (s m : ℕ) : Set Ω :=
  {ω | ENNReal.ofReal g₀ ≤ seed ω ∧ g₁ ≤ early ω ∧
    ∀ j < m-s, Real.exp (-kA*((s:ℝ)+j+1)) ≤ ∏ i∈Finset.range (j+1), q i ω}

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_FiniteStage
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

def finestCellWidth (H m : ℕ) : ℕ := H/(4*16^m)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CellRadiusComparison
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped Classical
namespace DirectionalTransience

noncomputable def stageCellStarts (He H w : ℕ) : Fin (((H-He)/w+1)+1) → ℕ :=
  Fin.lastCases H (fun j => He+j.val*w)
noncomputable def stageCellWidths (He H w wplus : ℕ) : Fin (((H-He)/w+1)+1) → ℕ :=
  Fin.lastCases wplus (fun _ => w)
noncomputable def stageCellGaps (He H w : ℕ) (Gminus Gplus : ℝ) : Fin (((H-He)/w+1)+1) → ℝ :=
  Fin.lastCases Gplus (fun _ => Gminus)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_LocalStoppedSplice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal Topology
namespace DirectionalTransience.ReferenceClasses

variable {H : Type*} [AddCommGroup H]

section Measurable
variable [Countable H] [TopologicalSpace H] [DiscreteTopology H]
  [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (OnePoint H)] [BorelSpace (OnePoint H)]

variable {R : Type*} [MeasurableSpace R]

abbrev UpperField (H R : Type*) := (ℕ × H) → R

end Measurable
end DirectionalTransience.ReferenceClasses

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IndependentDyadic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
namespace DirectionalTransience

lemma independent_dyadic_centered {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ a, Measurable (X a)) (hB : ∀ a ω, |X a ω|≤1) (hi : iIndepFun X μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun r : ℕ => sampleAverage X (2^r) ω-
      ∫ z, sampleAverage X (2^r) z ∂μ) atTop (𝓝 0) := by
  have hbound (n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε) :
      μ {ω | ε≤|sampleAverage X n ω-∫ z, sampleAverage X n z ∂μ|} ≤
        ENNReal.ofReal ((n:ℝ)⁻¹/ε^2) :=
    (meas_ge_le_variance_div_sq (sampleAverage_memLp μ X hX hB n) hε).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
        (sampleAverage_variance_le μ X hX hB hi n hn) (sq_nonneg _)))
  have hbc (k : ℕ) : ∀ᵐ ω ∂μ, ∀ᶠ r : ℕ in atTop,
      ¬ 1/(k+1:ℝ)≤|sampleAverage X (2^r) ω-∫ z, sampleAverage X (2^r) z ∂μ| := by
    apply ae_eventually_notMem
    have hs : Summable (fun r : ℕ => ((2^r:ℕ):ℝ)⁻¹/(1/(k+1:ℝ))^2) := by
      simpa only [Nat.cast_pow,Nat.cast_ofNat,←inv_pow] using
        (summable_geometric_of_norm_lt_one (show ‖(2:ℝ)⁻¹‖<1 by norm_num)).div_const ((1/(k+1:ℝ))^2)
    exact ne_top_of_le_ne_top hs.tsum_ofReal_lt_top.ne
      (ENNReal.tsum_le_tsum (fun r => hbound (2^r) (by positivity) _ (by positivity)))
  filter_upwards [ae_all_iff.mpr hbc] with ω hω
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hω k)
  refine ⟨N,fun r hr => ?_⟩
  simpa only [Real.dist_eq,sub_zero] using (lt_of_not_ge (hN r hr)).trans hk

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience.ReferenceClasses
variable {H R : Type*} [AddCommGroup H]

noncomputable def dustFrequency (dust : ℕ → Prop) (n : ℕ) : ℝ :=
  (n:ℝ)⁻¹*∑ a∈Finset.range n, if dust a then (1:ℝ) else 0

end DirectionalTransience.ReferenceClasses

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ReferenceContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace DirectionalTransience.ReferenceClasses

section Closed
variable {H : Type*} [AddCommGroup H] [TopologicalSpace H] [DiscreteTopology H]

omit [AddCommGroup H] in
lemma finite_value_clopen (z : H) : IsClopen ({(z : OnePoint H)} : Set (OnePoint H)) := by
  refine ⟨isClosed_singleton,?_⟩
  simpa only [Set.image_singleton] using
    (OnePoint.isOpenMap_coe {z} (isOpen_discrete _))

end Closed

end DirectionalTransience.ReferenceClasses

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

instance enat_borel : BorelSpace ℕ∞ := ⟨borel_eq_top_of_countable.symm⟩

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ClassSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma measurable_countable_selection {X I : Type*} [MeasurableSpace X]
    [MeasurableSpace I] [Countable I] [Nonempty I]
    (P : X → I → Prop) (hP : ∀ i, MeasurableSet {x | P x i}) :
    ∃ s : X → I, Measurable s ∧ ∀ x, (∃ i, P x i) → P x (s x) := by
  let : Encodable I := Encodable.ofCountable I
  let z : I := Classical.choice ‹Nonempty I›
  let enum : ℕ → I := fun n => (Encodable.decode (α := I) n).getD z
  have he : ∀ i : I, enum (Encodable.encode i)=i := by
    intro i
    simp only [enum,Encodable.encodek,Option.getD_some]
  let Q : X → ℕ → Prop := fun x n => P x (enum n) ∨ ¬∃ i, P x i
  have hQ : ∀ x, ∃ n, Q x n := by
    intro x
    by_cases h : ∃ i, P x i
    · obtain ⟨i,hi⟩ := h
      exact ⟨Encodable.encode i,Or.inl (by simpa only [he] using hi)⟩
    · exact ⟨0,Or.inr h⟩
  have hQm (n : ℕ) : MeasurableSet {x | Q x n} := by
    exact (hP (enum n)).union (by
      have hm : MeasurableSet {x | ∃ i, P x i} := by
        simpa only [Set.ofPred_exists] using MeasurableSet.iUnion hP
      exact hm.compl)
  refine ⟨fun x => enum (Nat.find (hQ x)), (measurable_of_countable enum).comp (measurable_find hQ hQm),?_⟩
  intro x hx
  exact (Nat.find_spec (hQ x)).resolve_right (not_not.mpr hx)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_BufferElapsedHeight
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def bufferWordHeight : List (ℕ × Bool) → ℕ
  | [] => 0
  | p::l => p.1+1+bufferWordHeight l

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CountableProdBind
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def bufferRetentionCost (R₀ g : ℝ) (κ : ℝ≥0) : ℝ≥0∞ :=
  ((κ:ℝ≥0∞)^2*ENNReal.ofReal g)*(κ:ℝ≥0∞)^(⌈max 0 R₀⌉₊+2)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_EventRate
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
variable {X : Type*} [MeasurableSpace X]

lemma measure_le_liminf_of_ae_eventually (μ : Measure X) (A : Set X) (hA : MeasurableSet A)
    (B : ℕ → Set X) (hB : ∀ k, MeasurableSet (B k))
    (he : ∀ᵐ x ∂μ, x∈A → ∀ᶠ k in atTop, x∈B k) :
    μ A≤liminf (fun k => μ (B k)) atTop := by
  calc
    μ A = ∫⁻ x, A.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by simp [hA]
    _ ≤ ∫⁻ x, liminf (fun k => (B k).indicator (fun _ => (1 : ℝ≥0∞)) x) atTop ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [he] with x hx
      by_cases ha : x∈A
      · rw [Set.indicator_of_mem ha]
        exact le_liminf_of_le (by isBoundedDefault) ((hx ha).mono fun k hk => by simp [hk])
      · simp [ha]
    _ ≤ liminf (fun k => ∫⁻ x, (B k).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ) atTop :=
      lintegral_liminf_le (fun k => measurable_const.indicator (hB k))
    _ = _ := by simp only [lintegral_indicator (hB _),lintegral_const,Measure.restrict_apply_univ,one_mul]

lemma event_rate (μ : Measure X) [IsProbabilityMeasure μ]
    (A : Set X) (hA : MeasurableSet A) (B : ℕ → Set X) (hB : ∀ k, MeasurableSet (B k))
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) {a C M : ℝ} (ha : 0<a) (hC : 0≤C)
    (hbound : ∀ k, μ.real (B k)*(a*(ns k:ℝ))≤C*(ns k:ℝ)+M)
    (he : ∀ᵐ x ∂μ, x∈A → ∀ᶠ k in atTop, x∈B k) :
    μ.real A≤C/a := by
  have hn : ∀ᶠ k in atTop, 0<(ns k:ℝ) := by
    simpa only [Nat.cast_pos] using hns.eventually (eventually_gt_atTop 0)
  have hb : ∀ᶠ k in atTop, μ (B k)≤ENNReal.ofReal (C/a+(M/a)/(ns k:ℝ)) := by
    filter_upwards [hn] with k hk
    rw [←ENNReal.ofReal_toReal (measure_ne_top μ (B k))]
    apply ENNReal.ofReal_le_ofReal
    have hh := (le_div_iff₀ (mul_pos ha hk)).mpr (hbound k)
    calc
      _ ≤ (C*(ns k:ℝ)+M)/(a*(ns k:ℝ)) := hh
      _ = _ := by field_simp
  have ht : Tendsto (fun k => ENNReal.ofReal (C/a+(M/a)/(ns k:ℝ))) atTop (𝓝 (ENNReal.ofReal (C/a))) := by
    simpa only [Function.comp_def,add_zero] using ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := C/a)).add
      ((tendsto_const_div_atTop_nhds_zero_nat (M/a)).comp hns))
  have hh := (measure_le_liminf_of_ae_eventually μ A hA B hB he).trans
    ((liminf_le_liminf hb).trans_eq ht.liminf_eq)
  exact ENNReal.toReal_le_of_le_ofReal (div_nonneg hC ha.le) hh

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal NNReal BigOperators Classical Topology
namespace DirectionalTransience

noncomputable def finiteOffsetTest {H : Type*} (z : H) (o : OnePoint H) : ℝ :=
  if o=(z:OnePoint H) then 1 else 0

lemma finiteOffsetTest_continuous {H : Type*} [TopologicalSpace H] [DiscreteTopology H]
    (z : H) : Continuous (finiteOffsetTest z) := by
  have ho : IsOpen ({(z:OnePoint H)} : Set (OnePoint H)) := by
    simpa only [Set.image_singleton] using OnePoint.isOpenMap_coe {z} (isOpen_discrete _)
  have hc : IsClosed ({(z:OnePoint H)} : Set (OnePoint H)) := isClosed_singleton
  apply continuous_iff_continuousAt.mpr
  intro o
  by_cases h : o=(z:OnePoint H)
  · apply (continuousAt_const (y:=(1:ℝ))).congr_of_eventuallyEq
    filter_upwards [ho.mem_nhds h] with x hx
    simp [finiteOffsetTest,Set.mem_singleton_iff.mp hx]
  · apply (continuousAt_const (y:=(0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hc.isOpen_compl.mem_nhds h] with x hx
    have hx' : x≠(z:OnePoint H) := hx
    simp [finiteOffsetTest,hx']

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_StationaryCompact
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace BoundedContinuousFunction
open scoped ENNReal Topology
namespace DirectionalTransience.StationaryCompact

variable {X Y : Type*} [MeasurableSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

noncomputable def episodeOccupationRaw (N : ℕ) (μ : Measure X)
    (A : X → Y) (M : X → ℕ) (T : Y → Y) : Measure Y :=
  ∑ i ∈ Finset.range N, (μ.restrict {x | i < M x}).map (fun x => T^[i] (A x))

instance episodeOccupationRaw_finite (N : ℕ) (μ : Measure X) [IsFiniteMeasure μ]
    (A : X → Y) (M : X → ℕ) (T : Y → Y) :
    IsFiniteMeasure (episodeOccupationRaw N μ A M T) := by
  unfold episodeOccupationRaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def episodeOccupation [Nonempty Y] (N : ℕ) (μ : Measure X) [IsFiniteMeasure μ]
    (A : X → Y) (M : X → ℕ) (T : Y → Y) : ProbabilityMeasure Y :=
  FiniteMeasure.normalize (⟨episodeOccupationRaw N μ A M T, (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩ : FiniteMeasure Y)

end DirectionalTransience.StationaryCompact

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeRetention
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

def StageRadiusOrder (r : ℝ → ℝ) (f b sfloor : ℝ) : Prop :=
  ∀ s, sfloor ≤ s → r (s*Real.exp (-f*b)) ≤ r s

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeExponential
attribute [-instance] _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

noncomputable def stagePotential (t : ℝ) (j f : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (t*(f:ℝ)-Real.exp (-t)*(j:ℝ)))

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayMarkTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

noncomputable def cutENNReal (B : ℝ≥0) : C(ℝ≥0∞,ℝ) :=
  ⟨fun x => (min x (B:ℝ≥0∞)).toReal, by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hf : min x (B:ℝ≥0∞) ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
    exact (ENNReal.continuousAt_toReal hf).comp (f:=fun y : ℝ≥0∞ => min y (B:ℝ≥0∞))
      (show ContinuousAt (fun y : ℝ≥0∞ => min y (B:ℝ≥0∞)) x from
        (continuous_id.min continuous_const).continuousAt)⟩

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_StationaryGrowth
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
namespace DirectionalTransience

noncomputable def orbitAverage {Ω : Type*} (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (n:ℝ)⁻¹ * ∑ i∈Finset.range n, f (T^[i] ω)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayMassSurvival
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma ennreal_negative_power_exp_lower {q : ℝ≥0∞} {lam t : ℝ} (hlam : 0≤lam)
    (hq : q≤ENNReal.ofReal (Real.exp (-t))) :
    ENNReal.ofReal (Real.exp (lam*t))≤q^(-lam) := by
  have h := ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hq hlam)
  rw [←ENNReal.rpow_neg,←ENNReal.rpow_neg] at h
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),Real.rpow_def_of_pos (Real.exp_pos _)] at h
  simpa only [Real.log_exp,neg_mul_neg,mul_comm] using h

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_ArrayGrowthEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma stationary_ae_integer_family {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (P : ℤ → Ω → Prop) (hp : ∀ i, MeasurableSet {ω | P i ω})
    (hs : ∀ i, ∀ᵐ ω ∂μ, P i (T ω) ↔ P (i+1) ω)
    (h0 : ∀ᵐ ω ∂μ, P 0 ω) : ∀ᵐ ω ∂μ, ∀ i, P i ω := by
  apply ae_all_iff.mpr
  have hb (i : ℤ) : (∀ᵐ ω ∂μ, P i ω) ↔ ∀ᵐ ω ∂μ, P (i+1) ω := by
    have he : (∀ᵐ ω ∂μ, P i (T ω)) ↔ ∀ᵐ ω ∂μ, P (i+1) ω := eventually_congr (hs i)
    rw [←ae_map_iff hT.measurable.aemeasurable (hp i),hT.map_eq] at he
    exact he
  intro i
  induction i using Int.induction_on with
  | zero => exact h0
  | succ n ih => exact (hb n).mp ih
  | pred n ih =>
    apply (hb (-(n:ℤ)-1)).mpr
    simpa only [sub_add_cancel] using ih

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_StationaryMonotone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace DirectionalTransience
lemma stationary_nat_monotone {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (N : Ω → ℕ) (hm : Measurable N) (hle : ∀ᵐ ω ∂μ, N ω≤N (T ω)) :
    ∀ᵐ ω ∂μ, N (T ω)=N ω := by
  let f := fun ω => (1:ℝ)/((N ω:ℝ)+1)
  have hfm : Measurable f := measurable_const.div (((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp hm).add_const 1)
  have hfi : Integrable f μ := by
    apply Integrable.mono' (integrable_const (1:ℝ)) hfm.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (by dsimp [f] <;> positivity)]
    exact (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (N ω) (α:=ℝ); linarith)
  have hcomp : Integrable (fun ω => f (T ω)) μ := (hT.integrable_comp hfm.aestronglyMeasurable).mpr hfi
  have hfl : ∀ᵐ ω ∂μ, f (T ω)≤f ω := by
    filter_upwards [hle] with ω hω
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hω 1)
  have hF : (fun ω => f (T ω))=ᵐ[μ] f :=
    (integral_eq_iff_of_ae_le hcomp hfi hfl).mp (by rw [←integral_map hT.measurable.aemeasurable hfm.aestronglyMeasurable,hT.map_eq])
  filter_upwards [hF] with ω hω
  have hh : (N (T ω):ℝ)+1=(N ω:ℝ)+1 := inv_inj.mp (by simpa only [f,one_div] using hω)
  exact_mod_cast (add_right_cancel hh : (N (T ω):ℝ)=(N ω:ℝ))
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_UniformFinsetKernel
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical BigOperators
namespace DirectionalTransience

lemma uniformFinset_eq {B : Type*} [MeasurableSpace B] [Countable B]
    [MeasurableSingletonClass B] (s : Finset B) (hs : s.Nonempty) :
    (PMF.uniformOfFinset s hs).toMeasure = (s.card:ℝ≥0∞)⁻¹ • ∑ b∈s, Measure.dirac b := by
  apply Measure.ext_of_singleton
  intro b
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b),PMF.uniformOfFinset_apply,
    Measure.smul_apply,Measure.finsetSum_apply]
  simp only [Measure.dirac_apply' _ (measurableSet_singleton b),smul_eq_mul]
  by_cases hb : b∈s
  · simp [hb]
  · simp [hb]

lemma uniformFinset_map {B C : Type*} [MeasurableSpace B] [MeasurableSpace C]
    [Countable B] [Countable C] [MeasurableSingletonClass B] [MeasurableSingletonClass C]
    (s : Finset B) (t : Finset C) (hs : s.Nonempty) (ht : t.Nonempty) (f : B → C)
    (hi : Set.InjOn f s) (he : s.image f=t) :
    ((PMF.uniformOfFinset s hs).toMeasure).map f=(PMF.uniformOfFinset t ht).toMeasure := by
  have hc : s.card=t.card := by rw [←he,Finset.card_image_iff.mpr hi]
  rw [uniformFinset_eq s hs,uniformFinset_eq t ht,
    Measure.map_smul,
    Measure.map_finset_sum (measurable_of_countable f).aemeasurable,hc]
  simp only [Measure.map_dirac]
  congr 1
  rw [←he,Finset.sum_image hi]

noncomputable def nonemptyFinsetKernel {B : Type*} [MeasurableSpace B]
    [Countable B] [MeasurableSingletonClass B] : Kernel {t : Finset B | t.Nonempty} B :=
  Kernel.ofFunOfCountable (fun t => (PMF.uniformOfFinset t.1 t.2).toMeasure)

noncomputable def uniformFinsetKernel {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Countable B] [MeasurableSingletonClass B] (s : A → Finset B)
    (hm : Measurable s) (hs : ∀ a, (s a).Nonempty) : Kernel A B :=
  nonemptyFinsetKernel.comap (fun a => ⟨s a,hs a⟩) (hm.subtype_mk (h := hs))

instance uniformFinsetKernel_markov {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Countable B] [MeasurableSingletonClass B] (s : A → Finset B)
    (hm : Measurable s) (hs : ∀ a, (s a).Nonempty) :
    IsMarkovKernel (uniformFinsetKernel s hm hs) where
  isProbabilityMeasure a := by change IsProbabilityMeasure (PMF.uniformOfFinset (s a) (hs a)).toMeasure; infer_instance

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_StationaryMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DirectionalTransience

lemma preserving_cond {A : Type*} [MeasurableSpace A] (μ : Measure A)
    {T : A → A} (hT : MeasurePreserving T μ μ) (E : Set A) (hE : MeasurableSet E)
    (hi : ∀ᵐ a ∂μ, T a∈E ↔ a∈E) : MeasurePreserving T μ[|E] μ[|E] := by
  have he : μ.restrict (T ⁻¹' E)=μ.restrict E := Measure.restrict_congr_set (hi.mono fun a ha => propext ha)
  have h := hT.restrict_preimage hE
  rw [he] at h
  exact h.smul_measure (μ E)⁻¹

lemma preserving_marking {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) [SFinite μ] {T : A → A} (hT : MeasurePreserving T μ μ)
    (K : Kernel A B) [IsSFiniteKernel K] (f : A × B → B) (hf : Measurable f)
    (he : ∀ᵐ a ∂μ, (K a).map (fun b => f (a,b))=K (T a)) :
    MeasurePreserving (fun p : A × B => (T p.1,f p)) (μ.compProd K) (μ.compProd K) := by
  have hm : Measurable (fun p : A × B => (T p.1,f p)) := (hT.measurable.comp measurable_fst).prodMk hf
  refine ⟨hm,?_⟩
  ext s hs
  rw [Measure.map_apply hm hs,Measure.compProd_apply (hs.preimage hm),Measure.compProd_apply hs]
  calc
    (∫⁻ a, K a (Prod.mk a ⁻¹' ((fun p : A × B => (T p.1,f p)) ⁻¹' s)) ∂μ) =
        ∫⁻ a, K (T a) (Prod.mk (T a) ⁻¹' s) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [he] with a ha
      rw [←ha,Measure.map_apply (show Measurable (fun b => f (a,b)) from hf.comp measurable_prodMk_left) (hs.preimage measurable_prodMk_left)]
      rfl
    _ = _ := hT.lintegral_comp (Kernel.measurable_kernel_prodMk_left hs)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_TailGrowth
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace TailGrowth

noncomputable def statistic (μ : Measure ℤ) (R : ℤ) : ℝ :=
  ⨆ j : ℤ, TailCuts.score (TailCuts.lower μ) (TailCuts.upper μ) R j

end TailGrowth

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_TailSampling
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace TailSampling

variable {D X : Type*} [MeasurableSpace D] [MeasurableSpace X]

noncomputable def cutKernel (w : Kernel D X) (S : ℤ → Set X)
    (hS : ∀ j, MeasurableSet (S j)) (j : D → ℤ) (hj : Measurable j) : Kernel D X where
  toFun d := (w d (S (j d)))⁻¹ • (w d).restrict (S (j d))
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have h₁ : Measurable (fun p : D × ℤ => w p.1 (S p.2)) :=
      measurable_from_prod_countable_left fun n => w.measurable_coe (hS n)
    have h₂ : Measurable (fun p : D × ℤ => w p.1 (A ∩ S p.2)) :=
      measurable_from_prod_countable_left fun n => w.measurable_coe (hA.inter (hS n))
    simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA]
    exact (h₁.comp (measurable_id.prodMk hj)).inv.mul
      (h₂.comp (measurable_id.prodMk hj))

end TailSampling

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_ProfileGrowth
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace TailGrowth

noncomputable def normalizedRestriction {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X) : Measure X := (μ s)⁻¹ • μ.restrict s

noncomputable def outwardMass {X : Type*} [MeasurableSpace X]
    (κ : Kernel X ℤ) (ξ : X → ℤ) (p : X × X) : ℝ :=
  ((κ p.1).prod (κ p.2)).real {y | ξ p.2 - ξ p.1 ≤ y.2-y.1}

end TailGrowth

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ProfileMeasureUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical BigOperators
namespace DirectionalTransience

lemma measure_le_of_atoms {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] {μ ν : Measure X} (h : ∀ x, μ {x}≤ν {x}) : μ≤ν := by
  apply Measure.le_iff.mpr
  intro s hs
  conv_lhs => rw [←μ.sum_smul_dirac]
  conv_rhs => rw [←ν.sum_smul_dirac]
  simp only [Measure.sum_apply _ hs,Measure.smul_apply,smul_eq_mul]
  apply ENNReal.tsum_le_tsum
  intro x
  exact mul_le_mul (h x) le_rfl zero_le zero_le

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RapidDecay
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def RapidDecay (a : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, Summable (fun n : ℕ => (n+1:ℝ)^m*a n)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_TailProfile
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace TailSampling

variable {D X : Type*} [MeasurableSpace D] [MeasurableSpace X]
    [MeasurableSingletonClass X]

noncomputable def lowerKernel (w : Kernel D X) (ξ : X → ℤ) (hξ : Measurable ξ)
    (j : D → ℤ) (hj : Measurable j) : Kernel D X :=
  cutKernel w (fun n => ξ ⁻¹' Set.Iic n) (fun _ => hξ measurableSet_Iic) j hj

noncomputable def upperKernel (w : Kernel D X) (ξ : X → ℤ) (hξ : Measurable ξ)
    (j : D → ℤ) (hj : Measurable j) : Kernel D X :=
  cutKernel w (fun n => ξ ⁻¹' Set.Ici n) (fun _ => hξ measurableSet_Ici) j hj

end TailSampling

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_Rows
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace TailDecorrelation

variable {I A D : Type*} [MeasurableSpace A] [MeasurableSpace D]

@[instance_reducible] def rows (S : Set I) : MeasurableSpace (I → A) :=
  ⨆ i : S, (inferInstance : MeasurableSpace A).comap (fun ω => ω i.1)

lemma rows_mono {S T : Set I} (h : S ⊆ T) :
    rows (A := A) S ≤ rows T := by
  apply iSup_le
  intro i
  exact le_iSup_of_le ⟨i.1, h i.2⟩ le_rfl

lemma rows_le (S : Set I) : rows (A := A) S ≤ (inferInstance : MeasurableSpace (I → A)) := by
  apply iSup_le
  intro i
  exact (show Measurable (fun ω : I → A => ω i.1) from
    measurable_pi_apply i.1).comap_le

@[instance_reducible] def dataRows (S : Set I) : MeasurableSpace (D × (I → A)) :=
  (inferInstance : MeasurableSpace D).comap Prod.fst ⊔
    (rows S).comap Prod.snd

lemma dataRows_mono {S T : Set I} (h : S ⊆ T) :
    dataRows (D := D) (A := A) S ≤ dataRows T := by
  exact sup_le_sup le_rfl (MeasurableSpace.comap_mono (rows_mono h))

lemma dataRows_le (S : Set I) : dataRows (D := D) (A := A) S ≤ (inferInstance : MeasurableSpace (D × (I → A))) := by
  exact sup_le_sup le_rfl (MeasurableSpace.comap_mono (rows_le S))

variable [Encodable I]

def prefixRows (n : ℕ) : Set I := {i | Encodable.encode i < n}

lemma prefixRows_mono : Monotone (prefixRows (I := I)) := by
  intro n m h i hi
  exact lt_of_lt_of_le hi h

noncomputable def dataFiltration : Filtration ℕ (inferInstance : MeasurableSpace (D × (I → A))) where
  seq n := dataRows (prefixRows n)
  mono' := fun _ _ h => dataRows_mono (prefixRows_mono h)
  le' n := dataRows_le (prefixRows n)

section BoundedIndependence

variable (δ : Measure D) (ν : Measure A) [IsProbabilityMeasure δ] [IsProbabilityMeasure ν]

def EscapingLocalApproximation (Z : ℕ → D × (I → A) → ℝ) (K : ℝ) : Prop :=
  ∀ η > 0, ∃ (W : ℕ → D × (I → A) → ℝ) (T : ℕ → D → Set I),
    (∀ n, Measurable (W n)) ∧
    (∀ n x, 0 ≤ W n x ∧ W n x ≤ K) ∧
    (∀ n d, @Measurable _ _ (rows (T n d)) _ (fun ω => W n (d, ω))) ∧
    (∀ n d, (∫ ω, |Z n (d, ω) - W n (d, ω)| ∂Measure.infinitePi (fun _ : I => ν)) ≤ η) ∧
    (∀ S : Set I, S.Finite → ∀ᵐ d ∂δ, ∀ᶠ n in atTop, Disjoint S (T n d))

end BoundedIndependence

end TailDecorrelation

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

end

end OAI
end


