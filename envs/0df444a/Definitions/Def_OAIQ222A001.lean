-- Prove2me | Definitions.Def_OAIQ222A001
-- name    : OAIQ222A001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:03:41.841849+00:00
-- url     : https://prove2.me/theorems/8da826dd-3abf-4822-b7d3-5fc88520f75e
-- title:
--   Definitions bundle OAIQ222A001 of the split of OpenAI, Exact quantum factoring over a fixed finite gate set (result family 279)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ExactQuantumFactoring.exact_quantum_factoring`, carved from OpenAI's openai/math development (OpenAI, *Exact quantum factoring over a fixed finite gate set (result family 279)*, OpenAI Math Release, September 25, 2026, result family 279, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 699 declarations of OpenAI's Lean: 543 definitions, 7 inductive types or structures, 27 instances and 122 theorems. The definitions and types are `OAI.ExactQuantumFactoring.AuxiliaryTree.advance`, `OAI.ExactQuantumFactoring.AuxiliaryTree.children`, `OAI.ExactQuantumFactoring.AuxiliaryTree.forest`, `OAI.ExactQuantumFactoring.AuxiliaryTree.level`, `OAI.ExactQuantumFactoring.AuxiliaryTree.preorder`, `OAI.ExactQuantumFactoring.AuxiliaryTree.run`, `OAI.ExactQuantumFactoring.AuxiliaryTree.seen`, `OAI.ExactQuantumFactoring.AuxiliaryTree.splitWeight`, `OAI.ExactQuantumFactoring.AuxiliaryTree.visits`, `OAI.ExactQuantumFactoring.BitArithmetic.ChildQueue.naturalKids`, `OAI.ExactQuantumFactoring.BitArithmetic.ChildQueue.oneBound`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.guardBound`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.nextBound`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.primeBound`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.quotientBound`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.splitBound`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.width`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.inWidth`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.outputBound`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.stepBound`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.width`, `OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.LEWord`, `OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.insert`, `OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.numbers`, `OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.sort`, `OAI.ExactQuantumFactoring.BitArithmetic.aksBranchBound`, `OAI.ExactQuantumFactoring.BitArithmetic.block`, `OAI.ExactQuantumFactoring.BitArithmetic.candidateProductBound`, `OAI.ExactQuantumFactoring.BitArithmetic.cfWidth`, `OAI.ExactQuantumFactoring.BitArithmetic.closedLevelBound`, `OAI.ExactQuantumFactoring.BitArithmetic.componentCongruenceBound`, `OAI.ExactQuantumFactoring.BitArithmetic.componentLevelBound`, `OAI.ExactQuantumFactoring.BitArithmetic.componentPhiBound`, `OAI.ExactQuantumFactoring.BitArithmetic.componentWidth`, `OAI.ExactQuantumFactoring.BitArithmetic.cyclicAddBound`, `OAI.ExactQuantumFactoring.BitArithmetic.cyclicMulBound`, `OAI.ExactQuantumFactoring.BitArithmetic.cyclicPowerWidth`, `OAI.ExactQuantumFactoring.BitArithmetic.cyclicStepBound`, `OAI.ExactQuantumFactoring.BitArithmetic.cyclicTestBound`, `OAI.ExactQuantumFactoring.BitArithmetic.euclidRun` and 510 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `QuantumFactoring_AKSBounds`, `QuantumFactoring_AppendRegister`, `QuantumFactoring_AuxiliaryData`, `QuantumFactoring_AuxiliaryTree`, `QuantumFactoring_BinLabelCircuit`, `QuantumFactoring_BinaryRoots`, `QuantumFactoring_BitArithmetic`, `QuantumFactoring_BitEncoding`, `QuantumFactoring_BitNumbers`, `QuantumFactoring_BitResidue`, `QuantumFactoring_BitStackAssociation`, `QuantumFactoring_BitStackBoundedPrime`, `QuantumFactoring_BitStackBoundedUnary`, `QuantumFactoring_BitStackDivision`, `QuantumFactoring_BitStackGCD`, `QuantumFactoring_BitStackIntegers`, `QuantumFactoring_BitStackListFlatten`, `QuantumFactoring_BitStackListMapIdx`, `QuantumFactoring_BitStackListOps`, `QuantumFactoring_BitStackListWords`, `QuantumFactoring_BitStackMultiplier`, `QuantumFactoring_BitStackOptions`, `QuantumFactoring_BitStackPowers`, `QuantumFactoring_BitStackPrograms`, `QuantumFactoring_BitStackRationalPower`, `QuantumFactoring_BitStackRationals`, `QuantumFactoring_BitStackUnary`, `QuantumFactoring_BooleanCircuit`, `QuantumFactoring_BooleanOracle`, `QuantumFactoring_BooleanProgram`, `QuantumFactoring_CRTLevels`, `QuantumFactoring_CanonicalResidueCircuit`, `QuantumFactoring_ChildQueueBounds`, `QuantumFactoring_ChildQueueCorrect`, `QuantumFactoring_CircuitEmissionModel`, `QuantumFactoring_CircuitSemantics`, `QuantumFactoring_CleanPermutation`, `QuantumFactoring_ClosedLevelCircuit`, `QuantumFactoring_CompletedOrderSlots`, `QuantumFactoring_CompletionFilterCircuit`, `QuantumFactoring_ComponentPhiCircuit`, `QuantumFactoring_ConcreteExpressionResources`, `QuantumFactoring_ContinuedFractionCircuit`, `QuantumFactoring_ContinuedFractionPairs`, `QuantumFactoring_ContinuedFractionRecovery`, `QuantumFactoring_ControlledHadamard`, `QuantumFactoring_ControlledTranslation`, `QuantumFactoring_CoveringPowerEmission`, `QuantumFactoring_CyclicAlgebra`, `QuantumFactoring_CyclicCircuit`, `QuantumFactoring_CyclicPowerCircuit`, `QuantumFactoring_CyclicTestBounds`, `QuantumFactoring_DivisorData`, `QuantumFactoring_DyadicCompletion`, `QuantumFactoring_DynamicMajorantExpressions`, `QuantumFactoring_EmissionBoundedRecursion`, `QuantumFactoring_EncodedStates`, `QuantumFactoring_Exactness`, `QuantumFactoring_ExactnessFurther`, `QuantumFactoring_ExactnessFurther2`, `QuantumFactoring_ExpressionAt`, `QuantumFactoring_ExpressionPostfix`, `QuantumFactoring_ExpressionPowerEmission`, `QuantumFactoring_ExpressionPredicates`, `QuantumFactoring_ExpressionResources`, `QuantumFactoring_ExpressionSharing`, `QuantumFactoring_ExpressionSyntaxEmission`, `QuantumFactoring_ExpressionTemplateCircuit`, `QuantumFactoring_ExpressionTemplateEmission`, `QuantumFactoring_ExpressionTokenProcedure`, `QuantumFactoring_FactorController`, `QuantumFactoring_FactorEncoding`, `QuantumFactoring_FactorSplitting`, `QuantumFactoring_FactorVerifierBounds`, `QuantumFactoring_FactoringCircuit`, `QuantumFactoring_FactoringRelabel`, `QuantumFactoring_FavorableSplit`, `QuantumFactoring_FilterExpressionSyntax`, `QuantumFactoring_FlatDataView`, `QuantumFactoring_FlatVerifiedData`, `QuantumFactoring_GateSemantics`, `QuantumFactoring_GcdCircuit`, `QuantumFactoring_HadamardAction`, `QuantumFactoring_InitialOrderState`, `QuantumFactoring_IntegerExpressions`, `QuantumFactoring_LabelRecoveryCircuit`, `QuantumFactoring_LevelCounts`, `QuantumFactoring_LevelIndependence`, `QuantumFactoring_ListSamplerCircuit`, `QuantumFactoring_MaskedPreparation`, `QuantumFactoring_MinimumCandidateCircuit`, `QuantumFactoring_ModularPower`, `QuantumFactoring_NativeAIGBounds`, `QuantumFactoring_NaturalExpressionCircuit`, `QuantumFactoring_NaturalExpressions`, `QuantumFactoring_NetworkEmissionBounds`, `QuantumFactoring_NetworkEmissionModel`, `QuantumFactoring_NetworkEmissionPair`, `QuantumFactoring_NetworkFoldChoiceEmission`, `QuantumFactoring_NodeControlBounds`, `QuantumFactoring_NodeControlCircuit`, `QuantumFactoring_NodeStateBounds`, `QuantumFactoring_NodeStateCircuit`, `QuantumFactoring_OccurrenceQueue`, `QuantumFactoring_OracleLayout`, `QuantumFactoring_OracleReadOnly`, `QuantumFactoring_OrderCandidateLaw`, `QuantumFactoring_OrderSampleCircuit`, `QuantumFactoring_OrderSamplerMass`, `QuantumFactoring_OrderTransition`, `QuantumFactoring_OrderTrial`, `QuantumFactoring_OrderTrialFurther`, `QuantumFactoring_OrderTrialFurther2`, `QuantumFactoring_OrderTrialLaw`, `QuantumFactoring_PackedPrograms`, `QuantumFactoring_ParallelPreparation`, `QuantumFactoring_PerfectPowerCircuit`, `QuantumFactoring_PhaseOracle`, `QuantumFactoring_PhasePreparation`, `QuantumFactoring_PhasePreparationConnection`, `QuantumFactoring_PhysicalAmplification`, `QuantumFactoring_PhysicalCompletionOutput`, `QuantumFactoring_PhysicalDataLog`, `QuantumFactoring_PhysicalListSlots`, `QuantumFactoring_PhysicalOrderSlots`, `QuantumFactoring_PhysicalSplit`, `QuantumFactoring_PhysicalTreeLaunch`, `QuantumFactoring_PhysicalTreeQueue`, `QuantumFactoring_PolyAt`, `QuantumFactoring_PolyBounds`, `QuantumFactoring_PolynomialExpressionResources`, `QuantumFactoring_PolynomialExpressions`, `QuantumFactoring_PolynomialFilterExpressions`, `QuantumFactoring_PreparedOracle`, `QuantumFactoring_Primality`, `QuantumFactoring_PrimalityAuxiliaryPrime`, `QuantumFactoring_PrimalityCorrectness`, `QuantumFactoring_PrimalityRootCount`, `QuantumFactoring_PrimeComponentCircuit`, `QuantumFactoring_PrimePowerLevels`, `QuantumFactoring_PrimeRecords`, `QuantumFactoring_ProductStates`, `QuantumFactoring_ProgressionEvaluation`, `QuantumFactoring_ProgressionExpressions`, `QuantumFactoring_ProvidedSplits`, `QuantumFactoring_QuantumCore`, `QuantumFactoring_QuarterPreparation`, `QuantumFactoring_QuarterRetentionEmission`, `QuantumFactoring_QueueCoverage`, `QuantumFactoring_RationalConditionals`, `QuantumFactoring_RationalExpressionResources`, `QuantumFactoring_RationalExpressions`, `QuantumFactoring_RationalHeightResources`, `QuantumFactoring_RationalPowerCircuit`, `QuantumFactoring_RationalRounding`, `QuantumFactoring_RawListRange`, `QuantumFactoring_RawTrialLabelCircuit`, `QuantumFactoring_ReadOnlyCircuit`, `QuantumFactoring_RecordedHistory`, `QuantumFactoring_RegisterBasis`, `QuantumFactoring_RegisterCircuit`, `QuantumFactoring_RepeatedTrials`, `QuantumFactoring_RetainedListFilter`, `QuantumFactoring_RetainedOrderFilter`, `QuantumFactoring_RetentionCircuit`, `QuantumFactoring_RetentionDenominators`, `QuantumFactoring_RetentionExpressions`, `QuantumFactoring_RetrospectiveCircuit`, `QuantumFactoring_RetrospectiveOrder`, `QuantumFactoring_RetrospectiveResidues`, `QuantumFactoring_RetrospectiveSlots`, `QuantumFactoring_RetrospectiveStatistics`, `QuantumFactoring_RootCircuit`, `QuantumFactoring_RowNetwork`, `QuantumFactoring_SignedSyntaxEmission`, `QuantumFactoring_SortedEncoding`, `QuantumFactoring_SortedWords`, `QuantumFactoring_SplitCandidate`, `QuantumFactoring_SuperpositionGates`, `QuantumFactoring_TableFavorable`, `QuantumFactoring_TableFavorableCount`, `QuantumFactoring_TableOrder`, `QuantumFactoring_TablePrimeSupport`, `QuantumFactoring_TableTotient`, `QuantumFactoring_TableTotientCircuit`, `QuantumFactoring_TensorPreparation`, `QuantumFactoring_TensorWiring`, `QuantumFactoring_ThresholdRetention`, `QuantumFactoring_TotientAccumulator`, `QuantumFactoring_TotientCircuit`, `QuantumFactoring_TraceBounds`, `QuantumFactoring_TransitionEqualization`, `QuantumFactoring_TransitionWords`, `QuantumFactoring_TreePadding`, `QuantumFactoring_TrialControlCircuit`, `QuantumFactoring_TrialControlEmission`, `QuantumFactoring_TrialRawPreparation`, `QuantumFactoring_TrialRetentionBounds`, `QuantumFactoring_TriangularAlgebra`, `QuantumFactoring_TriangularCircuit`, `QuantumFactoring_TriangularKernel`, `QuantumFactoring_TriangularPaths`, `QuantumFactoring_TriangularPreparation`, `QuantumFactoring_UniversalSplit`, `QuantumFactoring_VerifiedTableOrder`, `QuantumFactoring_VerifiedTreeBounds`, `QuantumFactoring_WordBlocks`.
--
--   **Imports.** It imports the published bundle `Def_ExactQuantumFactoring`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ222A002` and `OAIQ222A003`; the statement `OAI.ExactQuantumFactoring.Completion.orderSuccess_lower`.
-- source:
--   OpenAI, Exact quantum factoring over a fixed finite gate set (result family 279), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 279; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Exact-quantum-factoring-over-a-fixed-finite-gate-set-September-25-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Topology.Algebra.LinearMapCompletion
import Definitions.Def_ExactQuantumFactoring

section
-- module Solutions.OAIQ222_QF.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h

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
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_Primality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! Necessary exact primality component of Appendix A.  The tests are polynomial
congruences, not a primality oracle.  These lemmas start the appendix's actual
root-count proof; no polynomial-time implementation is assumed here. -/
namespace ExactQuantumFactoring.Primality
open Polynomial
open scoped BigOperators

/-- The evaluation form of an introspective exponent modulo X^s-1. -/
def Introspective {F : Type*} [CommRing F] (s k : ℕ) (f : F[X]) : Prop :=
  ∀ z : F, z^s = 1 → (f.eval z)^k = f.eval (z^k)

end ExactQuantumFactoring.Primality


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PrimalityRootCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring.Primality
open Polynomial
open scoped BigOperators

/-- The nonnegative exponent orbit. In a finite group this is the manuscript's H;
using its submonoid presentation makes the m^u p^v representatives explicit. -/
def residueOrbit (s m p : ℕ) : Submonoid (ZMod s) :=
  Submonoid.closure {(m : ZMod s), (p : ZMod s)}

noncomputable def residueRoot {F : Type*} [Field F] {s m p : ℕ}
    (w : F) (x : residueOrbit s m p) : F := w^x.val.val

noncomputable def subsetPolynomial {F : Type*} [Field F] (S : Finset F) : F[X] :=
  ∏ a ∈ S, (X-C a)

end ExactQuantumFactoring.Primality


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PrimalityCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring.Primality
open Polynomial
open scoped BigOperators

/-- The actual first rejection test in the appendix. -/
def PerfectPower (m : ℕ) : Prop := ∃ b e : ℕ, 2 ≤ b ∧ 2 ≤ e ∧ b^e = m

end ExactQuantumFactoring.Primality


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExactnessFurther
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ExactQuantumFactoring.Exactness
open scoped BigOperators

noncomputable def finiteInner {ι : Type*} [Fintype ι] (v w : ι → ℂ) : ℂ :=
  ∑ x, star (v x)*w x

noncomputable def outcomeMass {ι : Type*} [Fintype ι] (good : ι → Prop) (v : ι → ℂ) : ℝ := by
  classical
  exact ∑ x, if good x then Complex.normSq (v x) else 0

noncomputable def goodPart {ι : Type*} (good : ι → Prop) (v : ι → ℂ) : ι → ℂ := by
  classical
  exact fun x => if good x then v x else 0

noncomputable def stateReflection {ι : Type*} [Fintype ι] (ψ v : ι → ℂ) : ι → ℂ :=
  fun x => 2*finiteInner ψ v*ψ x-v x

end ExactQuantumFactoring.Exactness


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_GateSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring
open scoped BigOperators

noncomputable def Primitive.localMatrix (p : Primitive) :
    Matrix (Basis p.arity) (Basis p.arity) ℂ :=
  fun x y => p.matrix (List.ofFn x) (List.ofFn y)

/-- A reversible Boolean operation, viewed as an exact permutation matrix. -/
noncomputable def permutationMatrix {ι : Type*} [DecidableEq ι] (e : Equiv.Perm ι) :
    Matrix ι ι ℂ := Matrix.of (fun a b => if a = e b then 1 else 0)

def notPerm : Equiv.Perm (Basis 1) where
  toFun x := ![!x 0]
  invFun x := ![!x 0]
  left_inv x := by ext i; fin_cases i; simp
  right_inv x := by ext i; fin_cases i; simp

def cnotPerm : Equiv.Perm (Basis 2) where
  toFun x := ![x 0, Bool.xor (x 0) (x 1)]
  invFun x := ![x 0, Bool.xor (x 0) (x 1)]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp

def toffoliPerm : Equiv.Perm (Basis 3) where
  toFun x := ![x 0, x 1, Bool.xor (x 2) (x 0 && x 1)]
  invFun x := ![x 0, x 1, Bool.xor (x 2) (x 0 && x 1)]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp

noncomputable def controlledMatrix {ι : Type*} [DecidableEq ι] (A : Matrix ι ι ℂ) :
    Matrix (Bool × ι) (Bool × ι) ℂ :=
  Matrix.of (fun x y => if x.1 = y.1 then
    if x.1 then A x.2 y.2 else if x.2 = y.2 then 1 else 0
    else 0)

noncomputable def Gate.baseLocalMatrix (g : Gate) :
    Matrix (Basis g.primitive.arity) (Basis g.primitive.arity) ℂ :=
  Matrix.of (fun x y => g.baseMatrix (List.ofFn x) (List.ofFn y))

noncomputable def Gate.localMatrix (g : Gate) : Matrix (Basis g.arity) (Basis g.arity) ℂ :=
  Matrix.of (fun x y => g.matrix (List.ofFn x) (List.ofFn y))

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CircuitSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring
open scoped BigOperators Kronecker

abbrev Instruction.Unused {q : ℕ} (o : Instruction q) :=
  {i : Fin q // ∀ j, o.wire j ≠ i}

/-- Matrix of executing a list of instructions, in chronological order. -/
noncomputable def programMatrix {q : ℕ} (ops : List (Instruction q)) :
    Matrix (Basis q) (Basis q) ℂ :=
  ops.foldl (fun A (o : Instruction _) => o.matrix * A) 1

/-- Reversing a listed gate stays inside the same twenty gate names. -/
def Gate.reverse (g : Gate) : Gate := {g with inverse := !g.inverse}

def Instruction.reverse {q : ℕ} (o : Instruction q) : Instruction q :=
  ⟨o.gate.reverse, o.wire, o.distinct⟩

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring
open scoped BigOperators Kronecker

noncomputable def basisVector {ι : Type*} [DecidableEq ι] (x : ι) : ι → ℂ :=
  fun y => if y = x then 1 else 0

/-- No inverse/control flag is used in these elementary fresh-bit operations. -/
abbrev plainGate (p : Primitive) : Gate := ⟨p,false,false⟩

abbrev notAt {q : ℕ} (t : Fin q) : Instruction q :=
  ⟨plainGate .not, fun _ => t, by
    change Function.Injective (fun _ : Fin 1 => t)
    intro a b _
    exact Subsingleton.elim a b⟩

abbrev cnotAt {q : ℕ} (c t : Fin q) (hct : c ≠ t) : Instruction q :=
  ⟨plainGate .cnot, ![c,t], by
    change Function.Injective (![c,t] : Fin 2 → Fin q)
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all⟩

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring
open scoped BigOperators

/-- A Boolean node is implemented by at most two of the named fixed gates.
The target is excluded from the sources, but repeated sources are permitted.
Its action toggles the target, so the semantics are reversible on all states. -/
inductive BooleanOp (q : ℕ) (t : Fin q) where
  | constant (b : Bool)
  | copy (a : Fin q) (ha : a ≠ t)
  | neg (a : Fin q) (ha : a ≠ t)
  | conj (a b : Fin q) (ha : a ≠ t) (hb : b ≠ t)

namespace BooleanOp

def value {q : ℕ} {t : Fin q} : BooleanOp q t → Basis q → Bool
  | .constant b, _ => b
  | .copy a _, x => x a
  | .neg a _, x => !x a
  | .conj a b _ _, x => x a && x b

def eval {q : ℕ} {t : Fin q} (o : BooleanOp q t) (x : Basis q) : Basis q :=
  Function.update x t (Bool.xor (x t) (o.value x))

end BooleanOp

/-- The classical network explicitly retains all values already computed.
In a fresh-output DAG each node's target is a previously zero ancilla. -/
abbrev BooleanProgram (q : ℕ) := List ((t : Fin q) × BooleanOp q t)

def BooleanProgram.eval {q : ℕ} (p : BooleanProgram q) (x : Basis q) : Basis q :=
  p.foldl (fun x o => o.2.eval x) x

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- Little-endian computational wires, with the same bit ordering as the
manuscript and input/output interface. -/
def bitsValue : {b : ℕ} → (Fin b → Bool) → BitVec b
  | 0, _ => 0
  | b+1, x => BitVec.cons (x (Fin.last b)) (bitsValue (fun i => x i.castSucc))

lemma bitsValue_bit {b : ℕ} (x : Fin b → Bool) (i : Fin b) :
    (bitsValue x).getLsbD i.val = x i := by
  induction b with
  | zero => exact Fin.elim0 i
  | succ b ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [bitsValue, Fin.val_last, BitVec.getLsbD_cons, ite_true, if_true]
    · simp only [bitsValue, BitVec.getLsbD_cons, Fin.val_castSucc,
        ite_eq_right (Nat.ne_of_lt j.isLt)]
      exact ih _ j

lemma bitsValue_bits {b : ℕ} (x : BitVec b) :
    bitsValue (fun i : Fin b => x.getLsbD i.val) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact bitsValue_bit _ ⟨i,hi⟩

def bitsEquiv (b : ℕ) : (Fin b → Bool) ≃ BitVec b where
  toFun := bitsValue
  invFun := fun x i => x.getLsbD i.val
  left_inv := by intro x; funext i; exact bitsValue_bit x i
  right_inv := bitsValue_bits

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace BitArithmetic
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

def leftWord {w : ℕ} (x : Fin (w+w) → Bool) : BitVec w :=
  bitsValue (fun i => x (i.castAdd w))
def rightWord {w : ℕ} (x : Fin (w+w) → Bool) : BitVec w :=
  bitsValue (fun i => x (Fin.natAdd w i))

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitNumbers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

lemma bitsValue_toNat {b : ℕ} (x : Fin b → Bool) :
    (bitsValue x).toNat = ∑ i : Fin b, 2^i.val*(x i).toNat := by
  induction b with
  | zero => simp [bitsValue]
  | succ b ih =>
    rw [bitsValue, BitVec.toNat_cons', Nat.shiftLeft_eq, ih, Fin.sum_univ_castSucc]
    simp only [Fin.val_last, Fin.val_castSucc]
    ring

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ModularPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open scoped BigOperators

abbrev powerWidth (w b : ℕ) := ((w+w)+b)+w

def powerPack {w b : ℕ} (a m : Basis w) (e : Basis b) (z : Basis w) :
    Basis (powerWidth w b) := Fin.append (Fin.append (Fin.append a m) e) z

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TriangularPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators

abbrev Bits (b : ℕ) := Fin b → Bool

def hybrid {b : ℕ} (x y : Bits b) (k : ℕ) : Bits b :=
  fun i => if i.val < k then y i else x i

def TailEq {b : ℕ} (k : ℕ) (x y : Bits b) : Prop :=
  ∀ i : Fin b, k ≤ i.val → y i = x i

instance instDecidableTailEq {b k : ℕ} (x y : Bits b) : Decidable (TailEq k x y) := by
  unfold TailEq
  infer_instance

variable {A : Type*} [AddCommGroup A]

/-- Path translations for H on ascending physical wires followed by a
classically controlled translation on a separate additive register. -/
def pathShift {b : ℕ} (δ : Fin b → Bits b → A) (x y : Bits b) :
    (k : ℕ) → k ≤ b → A
  | 0, _ => 0
  | k+1, h => pathShift δ x y k (by omega) + δ ⟨k,by omega⟩ (hybrid x y (k+1))

noncomputable def hEntry (a c : Bool) : ℂ :=
  (if a && c then -1 else 1) / (Real.sqrt 2 : ℂ)

noncomputable def pathWeight {b : ℕ} (x y : Bits b) : (k : ℕ) → k ≤ b → ℂ
  | 0, _ => 1
  | k+1, h => pathWeight x y k (by omega) * hEntry (x ⟨k,by omega⟩) (y ⟨k,by omega⟩)

/-- Exact pointwise action of the H/conditional-forward-translation sequence.
There is no projection or forced-success operation in this evolution. -/
noncomputable def evolve {b : ℕ} (δ : Fin b → Bits b → A) (x : Bits b) (χ : A → ℂ) :
    (k : ℕ) → k ≤ b → Bits b → A → ℂ
  | 0, _, y, z => if y = x then χ z else 0
  | k+1, h, y, z =>
    (evolve δ x χ k (by omega) (Function.update y ⟨k,by omega⟩ false)
      (z-δ ⟨k,by omega⟩ y) +
     (if y ⟨k,by omega⟩ then (-1:ℂ) else 1) *
     evolve δ x χ k (by omega) (Function.update y ⟨k,by omega⟩ true)
      (z-δ ⟨k,by omega⟩ y)) / (Real.sqrt 2 : ℂ)

end ExactQuantumFactoring.Triangular


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TriangularAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators

def dot {b : ℕ} (x y : Bits b) : ℕ := ∑ i : Fin b, (x i).toNat*(y i).toNat

/-- The input word is reversed physically, while the output wire j is k_j. -/
def inputNumber {b : ℕ} (x : Bits b) : ℕ := ∑ i, 2^(b-1-i.val)*(x i).toNat
def outputNumber {b : ℕ} (y : Bits b) : ℕ := ∑ j, 2^j.val*(y j).toNat

def lowTerm {b : ℕ} (x y : Bits b) (i j : Fin b) : ℕ :=
  if j.val < i.val then 2^(b-1-i.val+j.val)*(x i).toNat*(y j).toNat else 0

def highTerm {b : ℕ} (x y : Bits b) (i j : Fin b) : ℕ :=
  if i.val < j.val then 2^(j.val-i.val-1)*(x i).toNat*(y j).toNat else 0

/-- One shift after H_j combines all the prescribed mutually commuting
controlled power-of-two shifts in that row. -/
def rowShift {b : ℕ} (j : Fin b) (z : Bits b) : ℕ :=
  ∑ i, if j.val < i.val then 2^(b-1-i.val+j.val)*(z i).toNat*(z j).toNat else 0

end ExactQuantumFactoring.Triangular


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring.Primality
open scoped BigOperators

/-- Exactly s coefficients with cyclic convolution, the concrete algebra
(Z/mZ)[X]/(X^s-1) used in the appendix. -/
abbrev Cyclic (R : Type*) [Semiring R] (s : ℕ) := AddMonoidAlgebra R (Fin s)

noncomputable def cyclicOf {R : Type*} [Semiring R] {s : ℕ} (v : Fin s → R) : Cyclic R s :=
  AddMonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm v)

@[simp] lemma cyclicOf_coeff {R : Type*} [Semiring R] {s : ℕ} (v : Fin s → R) (i : Fin s) :
    (cyclicOf v).coeff i = v i := rfl

/-- The residue class of X. No exponentially long polynomial is constructed. -/
noncomputable def cyclicX {R : Type*} [Semiring R] (s : ℕ) [NeZero s] : Cyclic R s :=
  AddMonoidAlgebra.single 1 1

noncomputable def cyclicC {R : Type*} [Semiring R] (s : ℕ) [NeZero s] (a : R) : Cyclic R s :=
  AddMonoidAlgebra.single 0 a

noncomputable def rootPower {F : Type*} [CommRing F] {s : ℕ} [NeZero s]
    (z : F) (hz : z^s=1) : Multiplicative (Fin s) →* F where
  toFun i := z^i.toAdd.val
  map_one' := by simp
  map_mul' i j := by
    change z^((i.toAdd+j.toAdd).val)=z^i.toAdd.val*z^j.toAdd.val
    rw [Fin.val_add,← pow_eq_pow_mod _ hz,pow_add]

noncomputable def cyclicEval {R F : Type*} [Semiring R] [CommRing F]
    {s : ℕ} [NeZero s] (f : R →+* F) (z : F) (hz : z^s=1) : Cyclic R s →+* F :=
  AddMonoidAlgebra.liftNCRingHom f (rootPower z hz) (fun _ _ => Commute.all _ _)

end ExactQuantumFactoring.Primality


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_WordBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open scoped BigOperators

def block {s w : ℕ} (x : Basis (s*w)) (i : Fin s) : Basis w :=
  fun j => x (finProdFinEquiv (i,j))

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open Primality
open scoped BigOperators

abbrev cyclicMulBound (s w ac bc mc : ℕ) : ℕ :=
  s*w*(w+s*(ac+bc+2*mc+(1224*w*w+143*w+12)+216*(w+1)^2+142*(w+1)+15))

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicPowerCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open Primality

abbrev cyclicPowerWidth (s w b : ℕ) := ((s*w+w)+b)+s*w

abbrev cyclicStepBound (s w : ℕ) :=
  cyclicMulBound s w (cyclicMulBound s w 0 0 0) 0 0 + cyclicMulBound s w 0 0 0+7*(s*w)

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicTestBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic

abbrev cyclicAddBound (s w ac bc mc : ℕ) :=
  s*w*(ac+bc+mc+216*(w+1)^2+142*(w+1)+15)

abbrev cyclicTestBound (s w : ℕ) :=
  cyclicAddBound s w (s*w*w) (s*w*w) 0+s*w*w+w*cyclicStepBound s w+
    cyclicAddBound s w (2*(s*w*w)+w*cyclicStepBound s w) (s*w*w) 0+96*(s*w)+21

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BinaryRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Bounded binary-root search required by the appendix's perfect-power check.
The search uses only comparisons and powers with exponent at most the input
bit bound; no unbounded Nat.nthRoot primitive is used by the algorithm. -/
namespace ExactQuantumFactoring.Primality

def rootSearch (m e : ℕ) : (k guess : ℕ) → ℕ
  | 0, guess => guess
  | k+1, guess =>
      let next := guess+2^k
      rootSearch m e k (if next^e ≤ m then next else guess)

def boundedRoot (m e n : ℕ) : ℕ := rootSearch m e n 0

end ExactQuantumFactoring.Primality


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RootCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic

/-- Width large enough for every candidate's e-th power, e≤n. -/
abbrev rootWidth (n : ℕ) := n*n+1

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PerfectPowerCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic

abbrev perfectCheckBound (n : ℕ) : ℕ :=
  147*rootWidth n+31+n*(230*rootWidth n+21+n*(90*rootWidth n*rootWidth n+14*rootWidth n+6))+
    n*(90*rootWidth n*rootWidth n+14*rootWidth n+6)

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PrimalityAuxiliaryPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace ExactQuantumFactoring.Primality
open scoped BigOperators

/-- The finite integer excluded by the auxiliary-prime search. -/
def badProduct (n m : ℕ) : ℕ := m * ∏ j ∈ Finset.Icc 1 (n^2), (m^j-1)

end ExactQuantumFactoring.Primality


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AKSBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic

abbrev aksBranchBound (n s w : ℕ) :=
  216*w*w+154*w+27+1 + (n^2*(100*w+23+w*(3672*w*w+436*w+36))+1) +
  (8*s*(216*w*w+203*w+38)+1) + (8*s*(cyclicTestBound s w+1)+1) + 3

abbrev primalityBound (n : ℕ) :=
  (n+1)*(perfectCheckBound n+4)+1+1 +
  ((n^8+1)*(aksBranchBound n (n^8) (rootWidth n)+4)+1)+1

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_EncodedStates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

/-- Embed a logical finite state in concrete basis words, including clean work. -/
noncomputable def encodeState {α : Type*} [Fintype α] {q : ℕ}
    (e : α → Basis q) (ψ : α → ℂ) : State q := by
  classical
  exact ∑ a, ψ a • basisVector (e a)

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RegisterCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators Kronecker

/-- A physical placement of a register uses distinct existing qubits. -/
abbrev Register (p q : ℕ) := Fin p ↪ Fin q

namespace Register

abbrev Unused {p q : ℕ} (w : Register p q) := {i : Fin q // ∀ j, w j ≠ i}

end Register

def Instruction.place {p q : ℕ} (w : Register p q) (o : Instruction p) : Instruction q :=
  ⟨o.gate, w ∘ o.wire, w.injective.comp o.distinct⟩

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RegisterBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- SWAP is three named CNOT gates, not an extra primitive. -/
def swapAt {q : ℕ} (a b : Fin q) (h : a ≠ b) : List (Instruction q) :=
  [cnotAt a b h, cnotAt b a h.symm, cnotAt a b h]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AppendRegister
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

def rightRegister (p q : ℕ) : Register q (p+q) := ⟨Fin.natAdd p, Fin.natAdd_injective q p⟩

def rightProgram {q : ℕ} (p : ℕ) (ops : List (Instruction q)) :
    List (Instruction (p+q)) := ops.map (Instruction.place (rightRegister p q))

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AuxiliaryTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Occurrence-preserving bounds for the canonical p−1 auxiliary tree in
Section5. Equal labels under different parents remain separate list entries. -/
namespace ExactQuantumFactoring.AuxiliaryTree
open scoped BigOperators

def children (M : ℕ) : List ℕ :=
  ((M.primeFactors.filter (fun p => 2<p)).sort (·≤·)).map (·-1)

lemma mem_children {M d : ℕ} : d ∈ children M ↔
    ∃ p, p.Prime ∧ p ∣ M ∧ M≠0 ∧ 2<p ∧ d=p-1 := by
  simp only [children,List.mem_map,Finset.mem_sort,Finset.mem_filter,Nat.mem_primeFactors]
  constructor
  · rintro ⟨p,⟨⟨hp,hpm,hM⟩,hp2⟩,hd⟩
    exact ⟨p,hp,hpm,hM,hp2,hd.symm⟩
  · rintro ⟨p,hp,hpm,hM,hp2,rfl⟩
    exact ⟨p,⟨⟨hp,hpm,hM⟩,hp2⟩,rfl⟩

lemma child_bounds {M d : ℕ} (hd : d ∈ children M) : 2≤d ∧ d<M := by
  obtain ⟨p,hp,hpm,hM,hp2,rfl⟩ := mem_children.mp hd
  have hpM := Nat.le_of_dvd (Nat.pos_of_ne_zero hM) hpm
  omega

/-- A level is a list, not a set: multiplicities of occurrences are retained. -/
def level (M : ℕ) : ℕ → List ℕ
  | 0 => [M]
  | k+1 => (children M).flatMap (fun d => level d k)

def splitWeight (M : ℕ) : ℕ := M.primeFactorsList.length

end ExactQuantumFactoring.AuxiliaryTree


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AuxiliaryData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree

/-- The source's distinct positive-exponent factor records. Finsupp stores each
prime once; its canonical serialization sorts its support in increasing order. -/
abbrev FactorRecord := ℕ→₀ℕ

inductive FactorData where
  | node (label : ℕ) (factors : FactorRecord) (descendants : List FactorData) : FactorData

def FactorData.label : FactorData→ℕ
  | .node m _ _ => m

def trueData (m : ℕ) : FactorData :=
  .node m m.factorization ((children m).attach.map (fun d => trueData d.val))
termination_by m
decreasing_by exact (child_bounds d.property).2

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_QuantumCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! Exact integer arithmetic for the prescribed-mass order trial.
These are dependencies of the actual main theorem, not assumptions about an
unknown order and not a replacement target. -/
namespace ExactQuantumFactoring.OrderTrial

open scoped BigOperators

/-- Number of integers x<Q congruent to t modulo d, when t<d≤Q. -/
def sampleCount (Q d t : ℕ) : ℕ := (Q-1-t)/d+1

/-- Literal nearest-bin rule floor(jQ/d+1/2), expressed entirely with integers. -/
def bin (Q d j : ℕ) : ℕ := (2*j*Q+d)/(2*d)

noncomputable def binError (Q d j : ℕ) : ℝ := (bin Q d j : ℝ) - (j:ℝ)*Q/d

end ExactQuantumFactoring.OrderTrial



/-! Dependencies for the actual prescribed-probability order trial.
The phase below is proved to be exactly the quarter-linear interpolant in
sections/03-order-transform.tex. No oracle/order information is input. -/
namespace ExactQuantumFactoring.OrderTrial

open scoped BigOperators
open MeasureTheory intervalIntegral

/-- Real triangular wave, period one; quotient norm makes continuity explicit. -/
noncomputable def triangle (x : ℝ) : ℝ := 1 - 4 * ‖(x : UnitAddCircle)‖

/-- Exact polygon phase, with clockwise orientation as in the forward shift. -/
noncomputable def phase (x : ℝ) : ℂ := ⟨triangle x, -triangle (x - 1/4)⟩

/-- The normalized interval average appearing in the dyadic majorant. -/
noncomputable def averagePhase (a η : ℝ) : ℂ :=
  ∫ v in (0 : ℝ)..1, phase (a+η*v)

/-- `I(u)` in equation (majorant-integral), without a restriction on u needed
for its analytic bounds. -/
noncomputable def residueIntegral (d : ℕ) (u η : ℝ) : ℂ :=
  (d : ℂ)⁻¹ * averagePhase (u/d) η

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ContinuedFractionRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Bounded Euclidean recovery of the manuscript's nearest-bin labels.
The denominator bound is logarithmic, never a search through B labels. -/
namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

/-- Euclid's finite convergent recurrence, entirely natural/rational arithmetic. -/
def euclidConvergent (a b : ℕ) : ℕ → ℚ
  | 0 => (a/b:ℕ)
  | k+1 => (a/b:ℕ)+(euclidConvergent b (a%b) k)⁻¹

/-- All label checks precede evaluation of any retention expression. -/
def IsBinLabel (Q B k : ℕ) (l : ℕ×ℕ) : Prop :=
  0<l.1 ∧ l.1<B ∧ l.2<l.1 ∧ Nat.Coprime l.2 l.1 ∧ bin Q l.1 l.2=k

instance instDecidableIsBinLabel (Q B k : ℕ) (l : ℕ×ℕ) : Decidable (IsBinLabel Q B k l) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def rationalLabel (q : ℚ) : ℕ×ℕ := (q.den,q.num.toNat)

/-- Search only the polynomially many Euclidean convergents. Rational labels
not satisfying the exact bin rule are rejected, not rounded into a candidate. -/
def recoveredLabels (s Q B k : ℕ) : List (ℕ×ℕ) :=
  ((List.range (2*s+1)).map (fun i => rationalLabel (euclidConvergent k Q i))).filter
    (fun l => decide (IsBinLabel Q B k l))

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ContinuedFractionPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial

/-- Reduced nonnegative numerator/positive denominator representation; the zero
case is essential because the total rational inverse sends zero to zero. -/
def convergentPair (a b : ℕ) : ℕ → ℕ×ℕ
  | 0 => (a/b,1)
  | k+1 =>
    let p := convergentPair b (a%b) k
    if p.1=0 then (a/b,1) else ((a/b)*p.1+p.2,p.1)

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactorSplitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- The actual representative used by bounded modular gcd arithmetic. -/
noncomputable def halfOrderResidue {m : ℕ} (a : (ZMod m)ˣ) : ℕ :=
  ((a ^ (orderOf a / 2) : (ZMod m)ˣ) : ZMod m).val

noncomputable def splitGcd {m : ℕ} (a : (ZMod m)ˣ) : ℕ :=
  Nat.gcd (halfOrderResidue a + m - 1) m

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_GcdCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Clocked Euclidean arithmetic, including zero operands.  The clock is
linear in bit width, and every step is an actual Boolean modular divider. -/
namespace ExactQuantumFactoring.BitArithmetic

def euclidRun : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0,a,b => (a,b)
  | k+1,a,b => if b=0 then (a,0) else euclidRun k b (a%b)

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SplitCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BitArithmetic

def candidateDivisor (m a d : ℕ) : ℕ :=
  if 0 < d ∧ 2 ∣ d then Nat.gcd (a^(d/2)%m+m-1) m else 0

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ContinuedFractionCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open OrderTrial

abbrev cfWidth (s k : ℕ) := s*(k+1)+1

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NaturalExpressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! A finite straight-line expression language for the exact rational formulas
in the manuscript. All values are natural numbers, not unit-cost hidden gates.
The following compiler will realize these operations with actual bit networks. -/
namespace ExactQuantumFactoring

inductive NatExpr (v : Type*) where
  | var : v → NatExpr v
  | const : ℕ → NatExpr v
  | add : NatExpr v → NatExpr v → NatExpr v
  | mul : NatExpr v → NatExpr v → NatExpr v
  | sub : NatExpr v → NatExpr v → NatExpr v
  | div : NatExpr v → NatExpr v → NatExpr v
  | mod : NatExpr v → NatExpr v → NatExpr v
  | iteLe : NatExpr v → NatExpr v → NatExpr v → NatExpr v → NatExpr v
  deriving Inhabited

namespace NatExpr
variable {v : Type*}

def eval (x : v → ℕ) : NatExpr v → ℕ
  | .var i => x i
  | .const c => c
  | .add a b => eval x a+eval x b
  | .mul a b => eval x a*eval x b
  | .sub a b => eval x a-eval x b
  | .div a b => eval x a/eval x b
  | .mod a b => eval x a%eval x b
  | .iteLe a b c d => if eval x a ≤ eval x b then eval x c else eval x d

def size : NatExpr v → ℕ
  | .var _ | .const _ => 1
  | .add a b | .mul a b | .sub a b | .div a b | .mod a b => size a+size b+1
  | .iteLe a b c d => size a+size b+size c+size d+1

def constOK (B : ℕ) : NatExpr v → Prop
  | .var _ => True
  | .const c => c < B
  | .add a b | .mul a b | .sub a b | .div a b | .mod a b => constOK B a ∧ constOK B b
  | .iteLe a b c d => constOK B a ∧ constOK B b ∧ constOK B c ∧ constOK B d

/-- Every intermediate value fits, not merely the eventual answer. -/
def Fits (B : ℕ) (x : v → ℕ) (e : NatExpr v) : Prop :=
  e.eval x < B ∧ match e with
    | .var _ | .const _ => True
    | .add a b | .mul a b | .sub a b | .div a b | .mod a b => Fits B x a ∧ Fits B x b
    | .iteLe a b c d => Fits B x a ∧ Fits B x b ∧ Fits B x c ∧ Fits B x d

end NatExpr
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NaturalExpressionCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BitArithmetic

namespace NatExpr
variable {v : Type*} {k w : ℕ}

def operationBound (w : ℕ) : ℕ := 300*w*w+1000*w+200

end NatExpr
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExpressionTemplateCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BitArithmetic
namespace NatExpr
variable {v : Type*}

def maxConst : NatExpr v → ℕ
  | .var _ => 0
  | .const c => c
  | .add a b | .mul a b | .sub a b | .div a b | .mod a b => _root_.Max.max a.maxConst b.maxConst
  | .iteLe a b c d => _root_.Max.max (_root_.Max.max a.maxConst b.maxConst) (_root_.Max.max c.maxConst d.maxConst)

def templateWidth (e : NatExpr v) (b : ℕ) : ℕ := (b+e.maxConst.size+1)*e.size

end NatExpr
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExpressionPredicates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BitArithmetic
namespace NatExpr
variable {v : Type*}

def testEq (a b : NatExpr v) (yes no : NatExpr v) : NatExpr v :=
  .iteLe a b (.iteLe b a yes no) no
end NatExpr
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BinLabelCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BitArithmetic

/-- Input order Q,B,k,d,j; coprimality is already guaranteed by the convergent
recurrence and does not require a second gcd computation. -/
def binCheckExpr : NatExpr (Fin 5) :=
  let Q := NatExpr.var 0
  let B := NatExpr.var 1
  let k := NatExpr.var 2
  let d := NatExpr.var 3
  let j := NatExpr.var 4
  let bin := NatExpr.div (.add (.mul (.mul (.const 2) j) Q) d) (.mul (.const 2) d)
  .iteLe (.const 1) d
    (.iteLe (.add d (.const 1)) B
      (.iteLe (.add j (.const 1)) d
        (.testEq bin k (.const 1) (.const 0)) (.const 0)) (.const 0)) (.const 0)

def checkedPair (Q B k i : ℕ) : ℕ×ℕ :=
  let p := convergentPair k Q i
  if IsBinLabel Q B k (p.2,p.1) then (p.2,p.1) else (0,0)

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderTrial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators
open MeasureTheory intervalIntegral

/-- Equation (order-P), before squaring the norm. -/
noncomputable def residueAmplitude (Q d j t : ℕ) : ℂ :=
  (Q:ℂ)⁻¹ * ∑ x ∈ (Finset.range Q).filter (fun x => x%d=t),
    phase ((bin Q d j:ℝ)*x/Q)

noncomputable def residueProbability (Q d j t : ℕ) : ℝ :=
  ‖residueAmplitude Q d j t‖^2

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators Topology
open Set Filter

/-- A positive-part square. This supplies a globally C¹ rational spline primitive. -/
noncomputable def rampSq (x : ℝ) : ℝ := (max 0 x)^2

noncomputable def splineRe (x : ℝ) : ℝ :=
  -(x+1/2)+2*(x+1/2)^2-4*rampSq x+4*rampSq (x-1/2)-4*rampSq (x-1)

noncomputable def splineIm (x : ℝ) : ℝ :=
  2*(x+1/2)^2-4*rampSq (x+1/4)+4*rampSq (x-1/4)-
    4*rampSq (x-3/4)+4*rampSq (x-5/4)-1/4

noncomputable def splineReDeriv (x : ℝ) : ℝ :=
  -1+4*(x+1/2)-8*max 0 x+8*max 0 (x-1/2)-8*max 0 (x-1)

noncomputable def splineImDeriv (x : ℝ) : ℝ :=
  4*(x+1/2)-8*max 0 (x+1/4)+8*max 0 (x-1/4)-
    8*max 0 (x-3/4)+8*max 0 (x-5/4)

noncomputable def spline (x : ℝ) : ℂ := (splineRe x : ℂ) + (splineIm x : ℂ)*Complex.I

end ExactQuantumFactoring.OrderTrial

namespace ExactQuantumFactoring.OrderTrial
open scoped Polynomial
open Polynomial MeasureTheory intervalIntegral

/-- Rational polynomial on a quarter interval; no real oracle is used in its data. -/
noncomputable def rampPiece (q a : ℤ) : ℚ[X] :=
  if a ≤ q then (X-C ((a:ℚ)/4))^2 else 0

noncomputable def evalReal (p : ℚ[X]) (x : ℝ) : ℝ := p.eval₂ (Rat.castHom ℝ) x

noncomputable def splineRePiece (q : ℤ) : ℚ[X] :=
  -(X+C (1/2))+ C 2*(X+C (1/2))^2 - C 4*rampPiece q 0 +
    C 4*rampPiece q 2 - C 4*rampPiece q 4

noncomputable def splineImPiece (q : ℤ) : ℚ[X] :=
  C 2*(X+C (1/2))^2-C 4*rampPiece q (-1)+C 4*rampPiece q 1-
    C 4*rampPiece q 3+C 4*rampPiece q 5-C (1/4)

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderTrialFurther
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ExactQuantumFactoring.OrderTrial
open scoped Polynomial
open Polynomial MeasureTheory intervalIntegral

noncomputable def rampLinear (q a : ℤ) : ℚ[X] := if a ≤ q then X-C ((a:ℚ)/4) else 0

noncomputable def phaseRePiece (q : ℤ) : ℚ[X] :=
  -1+C 4*(X+C (1/2))-C 8*rampLinear q 0+C 8*rampLinear q 2-C 8*rampLinear q 4
noncomputable def phaseImPiece (q : ℤ) : ℚ[X] :=
  C 4*(X+C (1/2))-C 8*rampLinear q (-1)+C 8*rampLinear q 1-
    C 8*rampLinear q 3+C 8*rampLinear q 5

end ExactQuantumFactoring.OrderTrial

namespace ExactQuantumFactoring.OrderTrial
open scoped Polynomial
open Polynomial

@[simp] lemma evalReal_add (p q : ℚ[X]) (x : ℝ) : evalReal (p+q) x = evalReal p x+evalReal q x :=
  Polynomial.eval₂_add _ _
@[simp] lemma evalReal_sub (p q : ℚ[X]) (x : ℝ) : evalReal (p-q) x = evalReal p x-evalReal q x :=
  Polynomial.eval₂_sub _
@[simp] lemma evalReal_mul (p q : ℚ[X]) (x : ℝ) : evalReal (p*q) x = evalReal p x*evalReal q x :=
  Polynomial.eval₂_mul _ _
@[simp] lemma evalReal_pow (p : ℚ[X]) (k : ℕ) (x : ℝ) : evalReal (p^k) x = (evalReal p x)^k :=
  Polynomial.eval₂_pow _ _ _
@[simp] lemma evalReal_C (a : ℚ) (x : ℝ) : evalReal (C a) x = (a:ℝ) :=
  Polynomial.eval₂_C _ _
@[simp] lemma evalReal_X (x : ℝ) : evalReal (X:ℚ[X]) x = x := Polynomial.eval₂_X _ _
@[simp] lemma evalReal_comp (p q : ℚ[X]) (x : ℝ) :
    evalReal (p.comp q) x = evalReal p (evalReal q x) := Polynomial.eval₂_comp _

noncomputable def linearArg (d : ℕ) (η : ℚ) : ℚ[X] := C ((d:ℚ)⁻¹)*X+C η

@[simp] lemma evalReal_linearArg (d : ℕ) (η : ℚ) (x : ℝ) :
    evalReal (linearArg d η) x = x/d + (η:ℝ) := by
  simp only [linearArg, evalReal_add, evalReal_mul, evalReal_C, evalReal_X,
    Rat.cast_inv, Rat.cast_natCast]
  ring

/-- The exact integral-coordinate polynomial, with the zero slope handled without division. -/
noncomputable def integralPiece (d : ℕ) (η : ℚ) (A G₀ G₁ : ℚ[X]) : ℚ[X] :=
  if η=0 then C ((d:ℚ)⁻¹)*A.comp (linearArg d 0)
  else C (((d:ℚ)*η)⁻¹)*(G₁.comp (linearArg d η)-G₀.comp (linearArg d 0))

noncomputable def massPiece (d : ℕ) (η : ℚ) (q₀ q₁ : ℤ) : ℚ[X] :=
  (integralPiece d η (phaseRePiece q₀) (splineRePiece q₀) (splineRePiece q₁))^2+
    (integralPiece d η (phaseImPiece q₀) (splineImPiece q₀) (splineImPiece q₁))^2

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators Polynomial
open Polynomial

/-- Upward coefficient rounding by a specified integer denominator. -/
def roundCoeff (D : ℕ) (a : ℚ) : ℚ := (⌈(D:ℚ)*a⌉:ℤ)/(D:ℚ)

noncomputable def roundedValue (D : ℕ) (p : ℚ[X]) (u : ℚ) : ℚ :=
  ∑ q ∈ Finset.range 5, roundCoeff D (p.coeff q)*u^q

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators Polynomial
open Polynomial

/-- Exact rational form of the nearest-bin error. -/
def binErrorRat (Q d j : ℕ) : ℚ := (bin Q d j : ℚ)-(j:ℚ)*Q/d

@[simp] lemma binErrorRat_cast (Q d j : ℕ) :
    (binErrorRat Q d j:ℝ) = binError Q d j := by simp [binErrorRat, binError]

/-- Half-open quarter assignment, computed only by rational arithmetic. -/
def quarterIndex (x : ℚ) : ℤ := ⌊4*x⌋

noncomputable def selectedMass (d : ℕ) (η u : ℚ) : ℚ[X] :=
  massPiece d η (quarterIndex (u/d)) (quarterIndex (u/d+η))

/-- Literal majorant from (majorant-construction), retaining Q and B as arguments. -/
noncomputable def majorant (Q B d j u : ℕ) : ℚ :=
  roundedValue (Q*B^8) (selectedMass d (binErrorRat Q d j) u) u + 64/(Q:ℚ)

/-- Source half-sum, initially a mathematical sum; bounded-piece evaluation follows. -/
noncomputable def majorantSum (Q B d j : ℕ) : ℚ :=
  (∑ u ∈ Finset.range d, majorant Q B d j u)/2

end ExactQuantumFactoring.OrderTrial



end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderTrialFurther2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators Polynomial
open Polynomial

/-- Integer numerator retained by upward rounding at an integer argument. -/
noncomputable def roundedNumerator (D : ℕ) (p : ℚ[X]) (u : ℕ) : ℤ :=
  ∑ q ∈ Finset.range 5, ⌈(D:ℚ)*p.coeff q⌉*(u:ℤ)^q

noncomputable def majorantNumerator (Q B d j u : ℕ) : ℤ :=
  roundedNumerator (Q*B^8) (selectedMass d (binErrorRat Q d j) u) u+64*(B:ℤ)^8

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

/-- Five closed power-sum formulas, not an enumeration up to the endpoint. -/
def powerSumValue (q : ℕ) (M : ℚ) : ℚ :=
  match q with
  | 0 => M
  | 1 => M*(M-1)/2
  | 2 => M*(M-1)*(2*M-1)/6
  | 3 => (M*(M-1)/2)^2
  | 4 => M*(M-1)*(2*M-1)*(3*M^2-3*M-1)/30
  | _ => 0

/-- Constant-length arithmetic formula for summing a degree-four expression. -/
def fiveTermSum (a : ℕ → ℚ) (lo hi : ℕ) : ℚ :=
  if lo ≤ hi then ∑ q ∈ Finset.range 5, a q*(powerSumValue q hi-powerSumValue q lo) else 0

/-- Clipped natural endpoints for the intersection of two rational intervals. -/
def intervalLo (a c : ℚ) : ℕ := max ⌈a⌉.toNat ⌈c⌉.toNat

def intervalHi (d : ℕ) (b e : ℚ) : ℕ := min d (min ⌈b⌉.toNat ⌈e⌉.toNat)

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators Polynomial
open Polynomial

/-- Exactly 32 possible quarter pairs. -/
noncomputable def quarterPairs : Finset (ℤ × ℤ) := (Finset.Ico 0 4) ×ˢ (Finset.Ico (-2) 6)

def pieceLabel (d : ℕ) (η : ℚ) (u : ℕ) : ℤ × ℤ :=
  (quarterIndex ((u:ℚ)/d), quarterIndex ((u:ℚ)/d+η))

def pieceLo (d : ℕ) (η : ℚ) (q : ℤ × ℤ) : ℕ :=
  intervalLo ((d:ℚ)*(q.1:ℚ)/4) ((d:ℚ)*((q.2:ℚ)/4-η))

def pieceHi (d : ℕ) (η : ℚ) (q : ℤ × ℤ) : ℕ :=
  intervalHi d ((d:ℚ)*((q.1:ℚ)+1)/4) ((d:ℚ)*(((q.2:ℚ)+1)/4-η))

/-- Each piece sum is computed with five closed power sums plus its length. -/
noncomputable def packedPieceSum (Q B d j : ℕ) (q : ℤ × ℤ) : ℚ :=
  let η := binErrorRat Q d j
  let lo := pieceLo d η q
  let hi := pieceHi d η q
  fiveTermSum (fun k => roundCoeff (Q*B^8) ((massPiece d η q.1 q.2).coeff k)) lo hi +
    ((hi-lo:ℕ):ℚ)*(64/(Q:ℚ))

/-- Exact constant-piece evaluation: no traversal of the d residues. -/
noncomputable def packedMajorantSum (Q B d j : ℕ) : ℚ :=
  (∑ q ∈ quarterPairs, packedPieceSum Q B d j q)/2

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

/-- Exact prescribed per-numerator mass, with the manuscript's ceiling. -/
def prescribedMass (d : ℕ) : ℚ := 1/(2:ℚ)^(Nat.clog 2 d+10)

/-- Downward dyadic ratio rounding, as in (mode-coefficient). -/
def modeCoeff (n : ℕ) (lam S : ℚ) : ℚ :=
  (⌊(2:ℚ)^(10*n)*(lam/S)⌋:ℤ)/(2:ℚ)^(10*n)

def modeRemainder (n : ℕ) (lam S : ℚ) : ℚ := lam-modeCoeff n lam S*S

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

/-- The three actual branches, including mode selection and uniform-label masses. -/
noncomputable def firstModeMass (n Q B d j : ℕ) : ℝ :=
  (modeCoeff n (prescribedMass d) (majorantSum Q B d j):ℝ)/2 *
    ∑ t ∈ Finset.range d, residueProbability Q d j t

noncomputable def secondModeMass (n Q B d j : ℕ) : ℝ :=
  (1/4) * ∑ t ∈ Finset.range d,
    (1/(B:ℝ)^3) * (2*(B:ℝ)^3 *
      ((majorant Q B d j ((j*t)%d):ℝ)-residueProbability Q d j t) *
      (modeCoeff n (prescribedMass d) (majorantSum Q B d j):ℝ))

noncomputable def thirdModeMass (n Q B d j : ℕ) : ℝ :=
  (1/4) * (1/(B:ℝ)^2) * (4*(B:ℝ)^2 *
    (modeRemainder n (prescribedMass d) (majorantSum Q B d j):ℝ))

end ExactQuantumFactoring.OrderTrial



end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_Exactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

/-- Integer arithmetic at grid points.  The only root of unity is -i. -/
def minusI : GaussianInt := ⟨0,-1⟩

def gridPhaseNumerator (Q y : ℕ) : GaussianInt :=
  ((Q-(4*y)%Q:ℕ):GaussianInt)*minusI^((4*y)/Q) +
    (((4*y)%Q:ℕ):GaussianInt)*minusI^((4*y)/Q+1)

/-- A literal finite integer sum, used to prove dyadicity independently of the
bounded-piece evaluator.  This sum is NOT asserted to be polynomial-time. -/
def residueGaussianNumerator (Q d j t : ℕ) : GaussianInt :=
  ∑ x ∈ (Finset.range Q).filter (fun x => x%d=t), gridPhaseNumerator Q (bin Q d j*x)

def residueProbabilityRat (Q d j t : ℕ) : ℚ :=
  ((residueGaussianNumerator Q d j t).norm:ℚ)/(Q:ℚ)^4

end ExactQuantumFactoring.OrderTrial

namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

noncomputable def phaseLabel (m y : ℕ) : ℂ := Complex.I^(y/m)

/-- Unnormalized correlation of the exactly prepared quarter-step state. -/
noncomputable def phaseOverlapSum (m D : ℕ) : ℂ :=
  ∑ y ∈ Finset.range (4*m), star (phaseLabel m ((y+D)%(4*m))) * phaseLabel m y

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

noncomputable def phaseState (m y : ℕ) : ℂ :=
  (Real.sqrt (4*(m:ℝ)):ℂ)⁻¹ * phaseLabel m y

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.Exactness
open scoped BigOperators

/-- Source (completion), with its actual downward integer rounding. -/
def completionCoeff (E : ℕ) (z A : ℚ) : ℚ :=
  (⌊(2:ℚ)^E*(z/A)⌋ : ℤ)/(2:ℚ)^E

def completionRemainder (E : ℕ) (z A : ℚ) : ℚ := z-completionCoeff E z A*A

/-- The second rounding of Section 6, independent of the transition algorithm. -/
def quarterCoeff (J : ℕ) (p : ℚ) : ℚ := completionCoeff (J+2) (1/2) p

def quarterRemainder (J : ℕ) (p : ℚ) : ℚ := 1/4-p*quarterCoeff J p/2

def knownProbability (n : ℕ) : ℚ := (1-1/(2:ℚ)^n)^(n^10)

end ExactQuantumFactoring.Exactness



end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SuperpositionGates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

abbrev phaseAt {q : ℕ} (t : Fin q) : Instruction q :=
  ⟨plainGate .phase, fun _ => t, by
    change Function.Injective (fun _ : Fin 1 => t)
    intro a b _; exact Subsingleton.elim a b⟩

abbrev hadamardAt {q : ℕ} (t : Fin q) : Instruction q :=
  ⟨plainGate .hadamard, fun _ => t, by
    change Function.Injective (fun _ : Fin 1 => t)
    intro a b _; exact Subsingleton.elim a b⟩

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhasePreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

/-- Hadamards on increasing physical wires; no multi-qubit gate abbreviation. -/
def hadamardPrefix (q : ℕ) : (k : ℕ) → k ≤ q → List (Instruction q)
  | 0, _ => []
  | k+1, h => hadamardPrefix q k (by omega) ++ [hadamardAt ⟨k, by omega⟩]

/-- The exact phase-state preparation from Section 3.1: H on every wire,
Z=S² on the most significant wire, and S on the next wire. -/
def preparePhase (b : ℕ) (hb : 2 ≤ b) : List (Instruction b) :=
  hadamardPrefix b b le_rfl ++
    [phaseAt ⟨b-1, by omega⟩, phaseAt ⟨b-1, by omega⟩, phaseAt ⟨b-2, by omega⟩]

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhasePreparationConnection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

/-- The physical wire basis is explicitly identified with the natural residue
labels; no implicit change in bit order is hidden in the overlap theorem. -/
def basisNumber (b : ℕ) : Basis b ≃ Fin (2^b) :=
  (bitsEquiv b).trans BitVec.equivFin.toEquiv

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitResidue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- The fixed little-endian physical representation of a modular residue. -/
def basisResidue (b : ℕ) : Basis b ≃ ZMod (2^b) :=
  (basisNumber b).trans (ZMod.finEquiv (2^b)).toEquiv

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

/-! A literal finite Boolean-stack compiler for circuit descriptions.
Branches inspect and consume one symbol, not an entire encoded word.
Operational derivations below count actual finite-state TM2 transitions.
-/
namespace ExactQuantumFactoring.BitStackProgram
open Turing.TM2 StateTransition

abbrev Config (K Λ : Type) := Cfg (fun _ : K => Bool) Λ (Option Bool)
def jump {K Λ : Type} (l : Λ) : Stmt (fun _ : K => Bool) Λ (Option Bool) :=
  .load (fun _ => none) (.goto (fun _ => l))
def dispatch {K Λ : Type} (k : K) (nil ff tt : Λ) :
    Stmt (fun _ : K => Bool) Λ (Option Bool) :=
  .pop k (fun _ b => b) (.branch Option.isSome
    (.branch (fun b => b.getD false) (jump tt) (jump ff)) (jump nil))

lemma iterate_step {α : Type*} (f : α → Option α) (a b : α) (h : f a=some b) :
    (flip bind f)^[1] (some a) = some b := h
lemma iterate_comp {α : Type*} (f : α → Option α) (a b c : α) (k l : ℕ)
    (h : (flip bind f)^[k] (some a)=some b)
    (g : (flip bind f)^[l] (some b)=some c) :
    (flip bind f)^[l+k] (some a)=some c := by
  rw [Function.iterate_add_apply,h,g]

end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackUnary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def addCounter (x : ℕ×ℕ) := (x.1,x.1+x.2)
lemma addCounter_iterate (i : ℕ) (x : ℕ×ℕ) :
    addCounter^[i] x=(x.1,i*x.1+x.2) := by
  induction i with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply',ih]
    simp only [addCounter,Prod.mk.injEq,true_and,Nat.succ_mul]
    omega

end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

lemma bits_length_add (a b : ℕ) : (a+b).bits.length≤a.bits.length+b.bits.length+1 := by
  rw [Nat.size_eq_bits_len,Nat.size_le]
  have ha:=Nat.lt_size_self a
  have hb:=Nat.lt_size_self b
  have hap : 2^a.size≤2^(a.bits.length+b.bits.length):=by
    apply Nat.pow_le_pow_right (by omega)
    simp only [Nat.size_eq_bits_len];omega
  have hbp : 2^b.size≤2^(a.bits.length+b.bits.length):=by
    apply Nat.pow_le_pow_right (by omega)
    simp only [Nat.size_eq_bits_len];omega
  rw [pow_succ]
  omega

lemma bits_length_mul (a b : ℕ) : (a*b).bits.length≤a.bits.length+b.bits.length := by
  rw [Nat.size_eq_bits_len,Nat.size_le,pow_add]
  have h:=Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self a) (Nat.lt_size_self b)
  simpa only [Nat.size_eq_bits_len] using h

lemma bits_length_pow2 (n : ℕ) : (2^n).bits.length=n+1 := by
  rw [Nat.size_eq_bits_len,Nat.size_pow]

def mulZeroStep (x : ℕ×ℕ) : ℕ×ℕ := (x.1,2*x.2)
def mulOneStep (x : ℕ×ℕ) : ℕ×ℕ := (x.1,2*x.2+x.1)

end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

abbrev DivState := ℕ×ℕ×ℕ

def divStep (b : Bool) (x : DivState) : DivState :=
  let t:=2*x.2.2+b.toNat
  if x.1≤t then (x.1,2*x.2.1+1,t-x.1) else (x.1,2*x.2.1,t)

lemma divStep_fst (b : Bool) (x : DivState) : (divStep b x).1=x.1 := by
  dsimp only [divStep];split <;> rfl

lemma divStep_spec (b : Bool) (x : DivState) (hr : x.2.2<x.1) :
    (divStep b x).2.2<x.1 ∧
      (divStep b x).2.1*x.1+(divStep b x).2.2=
        2*(x.2.1*x.1+x.2.2)+b.toNat := by
  have hb : b.toNat≤1:=by cases b <;> decide
  dsimp only [divStep]
  split
  · rename_i h
    have ht:=Nat.sub_add_cancel h
    dsimp only
    constructor <;> nlinarith
  · rename_i h
    dsimp only
    constructor <;> nlinarith

end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackListOps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}

lemma fold_map_cons_append (f : α→β) (xs : List α) (ys : List β) :
    xs.foldl (fun ys a=>f a::ys) ys=(xs.map f).reverse++ys := by
  induction xs generalizing ys with
  | nil=>rfl
  | cons a as ih=>simp only [List.foldl_cons,ih,List.map_cons,List.reverse_cons,
      List.append_assoc,List.singleton_append]

end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackOptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}
def optionCode (ea : α→List Bool) : Option α→List Bool
  | none=>[false]
  | some a=>true::ea a
def optionView : Option α→Unit⊕α
  | none=>.inl ()
  | some a=>.inr a
end ExactQuantumFactoring.BitStackProgram

end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackAssociation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type} [DecidableEq α]
def assocLookup (k : α) : List (α×β)→Option β
  | []=>none
  | (a,v)::as=>if k=a then some v else assocLookup k as
def assocStep (x : (α×β)×(α×Option β)) : α×Option β :=
  (x.2.1,if x.2.1=x.1.1 then some x.1.2 else x.2.2)
lemma assocFold_reverse (xs : List (α×β)) (k : α) (o : Option β) :
    xs.reverse.foldl (fun s a=>assocStep (a,s)) (k,o)=
      (k,match assocLookup k xs with | none=>o | some b=>some b) := by
  induction xs with
  | nil=>rfl
  | cons a as ih=>
    rw [List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil,ih]
    by_cases h:k=a.1 <;> simp [assocStep,assocLookup,h]
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackBoundedPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
lemma boolFold_eq (xs : List Bool) (b : Bool) :
    xs.foldl (fun b a=>a&&b) b=(xs.all id && b):=by
  induction xs generalizing b with
  | nil=>simp
  | cons a xs ih=>simp only [List.foldl_cons,ih,List.all_cons,id_eq];cases a <;> cases b <;> simp

end ExactQuantumFactoring.BitStackProgram
end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackBoundedUnary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def unaryDecodeStep (s : ℕ×ℕ) : ℕ×ℕ := if s.1=0 then s else (s.1-1,s.2+1)
lemma unaryDecodeStep_iterate (k : ℕ) (s : ℕ×ℕ) :
    (unaryDecodeStep^[k]) s=(s.1-k,s.2+min k s.1) := by
  induction k generalizing s with
  | zero=>simp
  | succ k ih=>
    rw [Function.iterate_succ_apply,ih]
    unfold unaryDecodeStep
    split
    · rename_i hz
      apply Prod.ext <;> dsimp only <;> omega
    · rename_i hz
      apply Prod.ext <;> dsimp only <;> omega
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackGCD
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def gcdStep (x : ℕ×ℕ) : ℕ×ℕ := if x.2=0 then x else (x.2,x.1%x.2)
def gcdRound (x : ℕ×ℕ) : ℕ×ℕ := gcdStep (gcdStep x)

lemma gcdStep_value (x : ℕ×ℕ) : (gcdStep x).1.gcd (gcdStep x).2=x.1.gcd x.2 := by
  unfold gcdStep
  split
  · rfl
  · dsimp only
    rw [Nat.gcd_comm x.2]
    exact (Nat.gcd_rec x.2 x.1).symm.trans (Nat.gcd_comm x.2 x.1)

lemma mod_half {b r : ℕ} (hr : 0 < r) (hlt : r<b) : b%r≤b/2 := by
  by_cases h : 2*r≤b
  · have ht:=Nat.mod_lt b hr
    omega
  · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega : b-r < r)]
    omega

lemma gcdRound_half (x : ℕ×ℕ) : (gcdRound x).2≤x.2/2 := by
  by_cases hb : x.2=0
  · simp [gcdRound,gcdStep,hb]
  · have hp : 0<x.2:=by omega
    have hr:=Nat.mod_lt x.1 hp
    by_cases hz : x.1%x.2=0
    · simp [gcdRound,gcdStep,hb,hz]
    · simp only [gcdRound,gcdStep,hb,ite_false, if_false,hz]
      exact mod_half (by omega) hr

lemma gcdRound_value (x : ℕ×ℕ) : (gcdRound x).1.gcd (gcdRound x).2=x.1.gcd x.2 := by
  rw [gcdRound,gcdStep_value,gcdStep_value]

lemma gcdRound_iterate_bound (i : ℕ) (x : ℕ×ℕ) :
    (gcdRound^[i] x).2≤x.2/2^i := by
  induction i with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply']
    calc
      (gcdRound (gcdRound^[i] x)).2≤(gcdRound^[i] x).2/2:=gcdRound_half _
      _≤(x.2/2^i)/2:=Nat.div_le_div_right ih
      _=x.2/2^(i+1):=by rw [Nat.div_div_eq_div_mul,pow_succ]

lemma gcdRound_iterate_value (i : ℕ) (x : ℕ×ℕ) :
    (gcdRound^[i] x).1.gcd (gcdRound^[i] x).2=x.1.gcd x.2 := by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply',gcdRound_value,ih]

lemma gcdRound_result (x : ℕ×ℕ) : (gcdRound^[x.2.bits.length] x).1=x.1.gcd x.2 := by
  have hz : (gcdRound^[x.2.bits.length] x).2=0:=by
    have hh:=gcdRound_iterate_bound x.2.bits.length x
    have hzdiv : x.2/2^x.2.bits.length=0:=by
      rw [Nat.size_eq_bits_len];exact Nat.div_eq_of_lt (Nat.lt_size_self x.2)
    rw [hzdiv] at hh
    omega
  simpa only [hz,Nat.gcd_zero_right] using gcdRound_iterate_value x.2.bits.length x


end ExactQuantumFactoring.BitStackProgram
end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackIntegers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def intData (z : ℤ) : Bool×ℕ := (decide (z<0),z.natAbs)
def intOfSign (x : Bool×ℕ) : ℤ := if x.1 then -(x.2 : ℤ) else (x.2 : ℤ)

lemma intOfSign_data (z : ℤ) : intOfSign (intData z)=z := by
  by_cases h : z<0
  · simp only [intData,intOfSign,h,decide_true,ite_true, if_true]
    exact (Int.eq_neg_natAbs_of_nonpos (le_of_lt h)).symm
  · simp only [intData,intOfSign,h,decide_false,Bool.false_eq_true,ite_false, if_false]
    exact Int.natAbs_of_nonneg (le_of_not_gt h)

lemma intData_ofSign (x : Bool×ℕ) :
    intData (intOfSign x)=(x.1 && decide (x.2≠0),x.2) := by
  rcases x with ⟨s,n⟩
  cases s <;> simp [intData,intOfSign,Nat.pos_iff_ne_zero]

def signedAdd (x : (Bool×ℕ)×(Bool×ℕ)) : Bool×ℕ :=
  if x.1.1=x.2.1 then (x.1.1,x.1.2+x.2.2)
  else if x.1.2≤x.2.2 then (x.2.1,x.2.2-x.1.2) else (x.1.1,x.1.2-x.2.2)

lemma signedAdd_value (x : (Bool×ℕ)×(Bool×ℕ)) :
    intOfSign (signedAdd x)=intOfSign x.1+intOfSign x.2 := by
  rcases x with ⟨⟨s,a⟩,⟨t,b⟩⟩
  cases s <;> cases t <;> simp only [signedAdd,intOfSign,Bool.false_eq_true,
    Bool.true_eq_false,ite_true, if_true,ite_false, if_false,Int.natCast_add]
  all_goals first | omega | (split <;> simp only [ite_true, if_true,Bool.false_eq_true,ite_false, if_false] <;> omega)

lemma signedMul_value (x : (Bool×ℕ)×(Bool×ℕ)) :
    intOfSign (xor x.1.1 x.2.1,x.1.2*x.2.2)=intOfSign x.1*intOfSign x.2 := by
  rcases x with ⟨⟨s,a⟩,⟨t,b⟩⟩
  cases s <;> cases t <;> simp [intOfSign]

lemma intOfSign_not (x : Bool×ℕ) : intOfSign (!x.1,x.2) = -intOfSign x := by
  rcases x with ⟨s,n⟩
  cases s <;> simp [intOfSign]

end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackListFlatten
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α : Type}
lemma fold_append_flatten (xss : List (List α)) (xs : List α) :
    xss.foldl (fun xs ys=>xs++ys) xs=xs++xss.flatten:=by
  induction xss generalizing xs with
  | nil=>simp
  | cons ys yss ih=>simp [ih,List.append_assoc]
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram

lemma nat_bits_length_bound (n : ℕ) : n.bits.length≤n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self
end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackListMapIdx
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β γ : Type}
lemma map_range_getD_index (xs : List β) (d : β) (f : ℕ→β→γ) :
    (List.range xs.length).map (fun i=>f i ((xs.drop i).headD d))=xs.mapIdx f:=by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i<xs.length:=by simpa using h1
    simp only [List.getElem_map,List.getElem_range,List.getElem_mapIdx]
    rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hi,Option.getD_some]
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackListWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
lemma fold_append_words (xs : List (List Bool)) (ys : List Bool) :
    xs.foldl (fun ys x=>ys++x) ys=ys++xs.flatten := by
  induction xs generalizing ys with
  | nil=>simp
  | cons x xs ih=>simp [ih,List.append_assoc]
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission

def attachIndex {m k : ℕ} (ρ : Fin m→Fin k) (i : ℕ) : ℕ :=
  if h : i < m then (ρ ⟨i,h⟩).val else k+(i-m)
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission

def pairIndex (n width i : ℕ) : ℕ:=if i<n then i else width+(i-n)
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram

lemma pairIndex_bound (n wa wb i : ℕ) (hn : n≤wa) (hi : i≤n+wb) :
    pairIndex n wa i≤wa+wb:=by unfold pairIndex;split <;> omega
lemma nat_bits_length_bound (n : ℕ) : n.bits.length≤n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RawListRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring
lemma ofFn_val_range (n : ℕ) : (List.ofFn fun i : Fin n => i.val) = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExpressionPostfix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram

/-- Variables, scalar constants, and the fixed algebra instruction vocabulary. -/
abbrev ExprToken (v : Type) := v ⊕ (ℕ ⊕ ℕ)
def pairToken {v : Type} : ExprToken v:=.inr (.inr 0)
def compToken {v : Type} : ExprToken v:=.inr (.inr 1)
def opToken {v : Type} (j : ℕ) : ExprToken v:=.inr (.inr (j+2))

def leTokens {v : Type} (a b : List (ExprToken v)) : List (ExprToken v):=
  ((b++a++[pairToken])++[opToken 5,compToken])++[opToken 6,compToken]
def muxTokens {v : Type} (c a b : List (ExprToken v)) : List (ExprToken v):=
  (((c++a++[pairToken])++b++[pairToken])++[opToken 7,compToken])

def exprTokens {v : Type} : NatExpr v→List (ExprToken v)
  | .var i=>[.inl i]
  | .const c=>[.inr (.inl c)]
  | .add a b=>((exprTokens a++exprTokens b++[pairToken])++[opToken 0,compToken])
  | .mul a b=>((exprTokens a++exprTokens b++[pairToken])++[opToken 1,compToken])
  | .sub a b=>muxTokens (leTokens (exprTokens b) (exprTokens a))
      ((exprTokens a++exprTokens b++[pairToken])++[opToken 2,compToken]) [.inr (.inl 0)]
  | .div a b=>((exprTokens a++exprTokens b++[pairToken])++[opToken 3,compToken])
  | .mod a b=>((exprTokens a++exprTokens b++[pairToken])++[opToken 4,compToken])
  | .iteLe a b c d=>muxTokens (leTokens (exprTokens a) (exprTokens b)) (exprTokens c) (exprTokens d)
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExpressionSyntaxEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram
variable {v : Type}
def exprView (e : NatExpr v) := (e.size,e.maxConst,exprTokens e)
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackPowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
lemma bits_length_pow (a k : ℕ) : (a^k).bits.length≤k*a.bits.length+1:=by
  induction k with
  | zero=>simp
  | succ k ih=>
    have h:=bits_length_mul (a^k) a
    rw [pow_succ];nlinarith

def powerStep (s : ℕ×ℕ) : ℕ×ℕ:=(s.1,s.2*s.1)
lemma powerStep_iterate (s : ℕ×ℕ) (i : ℕ) : (powerStep^[i]) s=(s.1,s.2*s.1^i):=by
  induction i with
  | zero=>simp
  | succ i ih=>rw [Function.iterate_succ_apply',ih];simp [powerStep,pow_succ,Nat.mul_assoc]
end ExactQuantumFactoring.BitStackProgram

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackRationals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def ratData (x : ℤ×ℕ) : ℤ×ℕ :=
  if x.2=0 then (0,1) else
    (intOfSign (decide (x.1<0),x.1.natAbs/(x.2.gcd x.1.natAbs)),
      x.2/(x.2.gcd x.1.natAbs))

lemma intOfSign_div (z : ℤ) (d : ℕ) (hd : d∣z.natAbs) :
    intOfSign (decide (z<0),z.natAbs/d)=z/(d : ℤ) := by
  by_cases h : z<0
  · have hz := Int.eq_neg_natAbs_of_nonpos (le_of_lt h)
    have hdiv : (d : ℤ) ∣ (z.natAbs : ℤ) := Int.ofNat_dvd.mpr hd
    simp only [h,decide_true,intOfSign,ite_true, if_true]
    conv_rhs => rw [hz,Int.neg_ediv_of_dvd hdiv]
    rw [Int.natCast_ediv]
  · simp only [h,decide_false,intOfSign,Bool.false_eq_true,ite_false, if_false]
    conv_rhs => rw [←Int.natAbs_of_nonneg (le_of_not_gt h)]
    rw [Int.natCast_ediv]

lemma ratData_spec (x : ℤ×ℕ) : ratData x=((mkRat x.1 x.2).num,(mkRat x.1 x.2).den) := by
  rw [Rat.num_mkRat,Rat.den_mkRat]
  unfold ratData
  split
  · rfl
  · rw [intOfSign_div _ _ (Nat.gcd_dvd_right _ _)]

end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitStackRationalPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
lemma intOfSign_pow (z : ℤ) (k : ℕ) :
    intOfSign (decide (z<0) && decide (k%2=1),z.natAbs^k)=z^k:=by
  by_cases hz:z<0
  · have he:=Int.eq_neg_natAbs_of_nonpos hz.le
    conv_rhs=>rw [he,neg_pow,neg_one_pow_eq_pow_mod_two]
    have hk:=Nat.mod_lt k (by omega : 0<2)
    have hp:k%2=0 ∨ k%2=1:=by omega
    rcases hp with h|h <;> simp [intOfSign,hz,h]
  · have he:=Int.natAbs_of_nonneg (le_of_not_gt hz)
    simp only [hz,decide_false,Bool.false_and,intOfSign,Bool.false_eq_true,ite_false, if_false,Int.natCast_pow,he]
end ExactQuantumFactoring.BitStackProgram

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

namespace BooleanNetwork

/-- Copy disjoint source wires into a separate target register, by XOR. -/
def copyPrefix {k m : ℕ} (source : Fin m → Fin k) : (t : ℕ) → t ≤ m → BooleanProgram (k+m)
  | 0, _ => []
  | t+1, h => copyPrefix source t (by omega) ++
    [⟨Fin.natAdd k ⟨t, by omega⟩, .copy ((source ⟨t, by omega⟩).castAdd m)
      (by intro he; have hh := congrArg Fin.val he; simp at hh; omega)⟩]

end BooleanNetwork
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_LevelIndependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


open scoped BigOperators
namespace ExactQuantumFactoring

noncomputable def equalLevelEquiv {A B T : Type*} (f : A → T) (g : B → T) :
    {x : A × B // f x.1 = g x.2} ≃ Σ b : B, {a : A // f a = g b} where
  toFun x := ⟨x.1.2, x.1.1, x.2⟩
  invFun x := ⟨(x.2.1,x.1),x.2.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

noncomputable def allEqualLevelEquiv {ι T : Type*} {G : ι → Type*} (i₀ : ι)
    (f : ∀ i, G i → T) :
    {x : ∀ i, G i // ∀ i, f i (x i) = f i₀ (x i₀)} ≃
      Σ t : T, ∀ i, {x : G i // f i x = t} where
  toFun x := ⟨f i₀ (x.1 i₀), fun i => ⟨x.1 i,x.2 i⟩⟩
  invFun x := ⟨fun i => (x.2 i).1, fun i => (x.2 i).2.trans (x.2 i₀).2.symm⟩
  left_inv x := rfl
  right_inv x := by
    rcases x with ⟨t,x⟩
    dsimp
    have he : f i₀ (x i₀).1 = t := (x i₀).2
    apply Sigma.ext he
    have hh : ∀ (s t : T) (a : ∀ i, {z : G i // f i z = s})
        (b : ∀ i, {z : G i // f i z = t}), s = t →
        (∀ i, (a i).val = (b i).val) → HEq a b := by
      rintro s t a b rfl hab
      apply heq_of_eq
      funext i
      exact Subtype.ext (hab i)
    exact hh _ _ _ _ he (fun _ => rfl)

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_LevelCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


open scoped BigOperators
namespace ExactQuantumFactoring

noncomputable def cumulativeLevelCount (G : Type*) [Group G] [Fintype G] (t : ℕ) : ℕ := by
  classical
  exact Fintype.card {x : G // padicValNat 2 (orderOf x) ≤ t}

noncomputable def levelCount (G : Type*) [Group G] [Fintype G] (t : ℕ) : ℕ := by
  classical
  exact Fintype.card {x : G // padicValNat 2 (orderOf x) = t}

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PrimePowerLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

/-- A closed integer expression; no enumeration of residue classes. -/
def primePowerUnitCount (p e : ℕ) : ℕ := (p-1) * p^(e-1)

def closedLevelCount (R t : ℕ) : ℕ :=
  if t = 0 then R / 2^padicValNat 2 R
  else if t ≤ padicValNat 2 R then 2^(t-1) * (R / 2^padicValNat 2 R) else 0

noncomputable def primePowerLevelCard (p e t : ℕ) : ℕ :=
  Nat.card {x : (ZMod (p^e))ˣ // padicValNat 2 (orderOf x) = t}

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CRTLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


open scoped BigOperators
namespace ExactQuantumFactoring

abbrev Component (m : ℕ) := {p : ℕ // p ∈ m.primeFactors}

instance componentNeZero (m : ℕ) (p : Component m) :
    NeZero (p.val ^ m.factorization p.val) :=
  ⟨pow_ne_zero _ (Nat.mem_primeFactors.mp p.property).1.ne_zero⟩

abbrev ComponentUnits (m : ℕ) (p : Component m) :=
  (ZMod (p.val ^ m.factorization p.val))ˣ

noncomputable def unitCRT (m : ℕ) (hm : m ≠ 0) :
    (ZMod m)ˣ ≃* (∀ p : Component m, ComponentUnits m p) :=
  (Units.mapEquiv (ZMod.equivPi m hm).toMulEquiv).trans MulEquiv.piUnits

lemma component_order_level_lt {m n : ℕ} (hm : m ≠ 0) (hmn : m < 2^n)
    (p : Component m) (a : ComponentUnits m p) : padicValNat 2 (orderOf a) < n := by
  have ho : 0 < orderOf a := orderOf_pos a
  have hpow : 2^padicValNat 2 (orderOf a) ≤ orderOf a := Nat.le_of_dvd ho pow_padicValNat_dvd
  have hcard : Nat.card (ComponentUnits m p) = (p.val ^ m.factorization p.val).totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
  calc
    _ ≤ orderOf a := hpow
    _ ≤ Nat.card (ComponentUnits m p) := orderOf_le_card
    _ = _ := hcard
    _ ≤ p.val ^ m.factorization p.val := Nat.totient_le _
    _ ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.ordProj_dvd _ _)
    _ < 2^n := hmn

noncomputable def componentLevel {m n : ℕ} (hm : m ≠ 0) (hmn : m < 2^n)
    (p : Component m) (a : ComponentUnits m p) : Fin (n+1) :=
  ⟨padicValNat 2 (orderOf a), by have := component_order_level_lt hm hmn p a; omega⟩

/-- Closed form for the number of favorable unit residues. Only n+1 levels
and the prime-power factors occur; there is no modulo-m residue enumeration. -/
def favorableCount (m n : ℕ) : ℕ :=
  m.totient - ∑ t : Fin (n+1), ∏ p : Component m,
    closedLevelCount (primePowerUnitCount p.val (m.factorization p.val)) t.val

noncomputable def FavorableUnit {m n : ℕ} (hm : m ≠ 0) (hmn : m < 2^n)
    (p₀ : Component m) (a : (ZMod m)ˣ) : Prop :=
  ¬ ∀ p, componentLevel hm hmn p (unitCRT m hm a p) =
    componentLevel hm hmn p₀ (unitCRT m hm a p₀)

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactorEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- Zero padding follows every positive entry. -/
def PaddedOrder (a b : ℕ) : Prop := b=0 ∨ (a≠0 ∧ a≤b)

def unpadProduct (xs : List ℕ) : ℕ := (xs.map (fun a => if a=0 then 1 else a)).prod

def FactorListValid (N : ℕ) (xs : List ℕ) : Prop :=
  (∀ a ∈ xs, a=0 ∨ a.Prime) ∧ xs.Pairwise PaddedOrder ∧ unpadProduct xs=N

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactorVerifierBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

abbrev candidateProductBound (n c : ℕ) :=
  n*(2*c+105*n+21+rootWidth n+90*rootWidth n*rootWidth n+14*rootWidth n+6)+rootWidth n

abbrev factorVerifierBound (n c : ℕ) :=
  n*(2*c+146*n+35+rootWidth n+primalityBound n+1)+1+
  (n*n*(4*c+242*n+58)+1)+1+
  (candidateProductBound n c+c+rootWidth n+96*rootWidth n+21)+1

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PrimeComponentCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork

namespace BitArithmetic
/-- A polynomial-width, polynomial-size component modulus circuit. It uses
p as an input prime, not an oracle or enumeration of prime factors of m. -/
def componentWidth (n : ℕ) : ℕ := n*n+1

def primeComponentBound (n c : ℕ) : ℕ :=
  let w:=componentWidth n
  c+w+(w+n*(c+w+90*w*w+14*w+6))+2*w*(216*w*w+300*w+100)+n

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PrimeRecords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

noncomputable def primeRecord : List ℕ→FactorRecord
  | [] => 0
  | p::ps => Finsupp.single p 1+primeRecord ps

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetrospectiveOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

/-- One occurrence of the source's prime-stripping loop. A repeated prime
factor list supplies exactly as many attempts as its known multiplicity. -/
def stripOrderPrime {G : Type*} [Monoid G] [DecidableEq G] (a : G) (q v : ℕ) : ℕ :=
  if q ∣ v ∧ a^(v/q)=1 then v/q else v

def stripOrderFactors {G : Type*} [Monoid G] [DecidableEq G] (a : G) : List ℕ→ℕ→ℕ
  | [], v => v
  | q::qs, v => stripOrderFactors a qs (stripOrderPrime a q v)

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_DivisorData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open AuxiliaryTree

/-- Expand ONLY the supplied exponent record. No factoring operation is hidden
in the list used by the retrospective controller. -/
def recordPrimes (f : FactorRecord) : List ℕ :=
  (f.support.sort (· ≤ ·)).flatMap (fun p => List.replicate (f p) p)

/-- Divide a subfactor from the parent's prime list, in bounded time: there is
at most one division per prime occurrence in the already supplied list. -/
def divisorPrimes : ℕ→List ℕ→List ℕ
  | _, [] => []
  | m, p::ps => if p∣m then p::divisorPrimes (m/p) ps else divisorPrimes m ps

/-- Literal stored record projection, used only after complete-data validation. -/
def FactorData.factors : FactorData→FactorRecord
  | .node _ f _ => f

def FactorData.descendants : FactorData→List FactorData
  | .node _ _ ds => ds

def dataDivisorPrimes (data : FactorData) (m : ℕ) : List ℕ :=
  divisorPrimes m (recordPrimes data.factors)

/-- Child lookup takes the first matching stored occurrence. It does not compute
new children. Distinct parents deliberately retain separate occurrence data. -/
def dataChildPrimes (data : FactorData) (label : ℕ) : List ℕ :=
  match data.descendants.find? (fun d => decide (d.label=label)) with
  | none => []
  | some d => recordPrimes d.factors

/-- phi factors are reconstructed from division against the supplied parent
record and the supplied p−1 children. The p=2 contribution requires no child. -/
noncomputable def dataTotientPrimes (data : FactorData) (m : ℕ) : List ℕ :=
  let f := primeRecord (dataDivisorPrimes data m)
  (f.support.sort (· ≤ ·)).flatMap (fun p =>
    List.replicate (f p-1) p ++ if p=2 then [] else dataChildPrimes data (p-1))

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetrospectiveCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic

def stripPrimeNat (a m q v : ℕ) : ℕ :=
  if v%q=0 ∧ a^(v/q)%m=1 then v/q else v

namespace BitArithmetic

def stripStepBound (w c : ℕ) : ℕ := 9*c+4000*w^3+1500*w^2+500*w+100

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RepeatedTrials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


/-! Exact independent-trial laws and the source's K=n^5 success guarantee. -/
namespace ExactQuantumFactoring.RepeatedTrials
open scoped BigOperators
open ExactQuantumFactoring.Exactness

noncomputable def tensorState {α : Type*} (ψ : α→ℂ) (K : ℕ) (x : Fin K→α) : ℂ :=
  ∏ i, ψ (x i)

end ExactQuantumFactoring.RepeatedTrials


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OracleLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork

/-- Input, output, then zero work space; this same layout is used by the
classical subroutines inside the coherent controller. -/
def packed {n m : ℕ} (r : ℕ) (x : Basis n) (y : Basis m) : Basis (n+m+r) :=
  fun i => if h : i.val < n then x ⟨i.val,h⟩
    else if h' : i.val < n+m then y ⟨i.val-n,by omega⟩ else false

def oracleIndex (n m width i : ℕ) : ℕ :=
  if i < n then i else if i < width then n+m+(i-n) else n+(i-width)

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PackedPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork

def firstRegister (n m r : ℕ) : Register n (n+m+r) where
  toFun i := ⟨i.val,by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun t : Fin (n+m+r) => t.val) h

def firstProgram {n : ℕ} (m r : ℕ) (ops : List (Instruction n)) :
    List (Instruction (n+m+r)) := ops.map (Instruction.place (firstRegister n m r))

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CleanPermutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork

def swapPrefix (n r : ℕ) : (k : ℕ) → k ≤ n → List (Instruction (n+n+r))
  | 0, _ => []
  | k+1, h => swapPrefix n r k (by omega) ++
      swapAt ⟨k,by omega⟩ ⟨n+k,by omega⟩ (by intro he; have hh := congrArg Fin.val he; dsimp at hh; omega)

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ControlledTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork

namespace ControlledTranslation

def dataPart {p b : ℕ} (x : Basis (p+b)) : Basis p := fun i => x (i.castAdd b)
def phasePart {p b : ℕ} (x : Basis (p+b)) : Basis b := fun i => x (Fin.natAdd p i)

def translate {p b : ℕ} (δ : Basis p → BitVec b) (x : Basis (p+b)) : Basis (p+b) :=
  Fin.append (dataPart x) (fun i => (bitsValue (phasePart x) + δ (dataPart x)).getLsbD i.val)

def untranslate {p b : ℕ} (δ : Basis p → BitVec b) (x : Basis (p+b)) : Basis (p+b) :=
  Fin.append (dataPart x) (fun i => (bitsValue (phasePart x) - δ (dataPart x)).getLsbD i.val)

@[simp] lemma dataPart_append {p b : ℕ} (d : Basis p) (z : Basis b) :
    dataPart (Fin.append d z) = d := by funext i; simp [dataPart]
@[simp] lemma phasePart_append {p b : ℕ} (d : Basis p) (z : Basis b) :
    phasePart (Fin.append d z) = z := by funext i; simp [phasePart]

end ControlledTranslation
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_HadamardAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

noncomputable def localHadamard {A : Type*} [Fintype A] {b : ℕ} (j : Fin b) :
    Matrix (Basis b × A) (Basis b × A) ℂ := by
  classical
  exact fun v u => if v.2=u.2 then (hadamardAt j).matrix v.1 u.1 else 0

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RowNetwork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators
open BooleanNetwork

def rowIndex {b : ℕ} (j e : Fin b) : Fin b :=
  ⟨(b-1+j.val-e.val)%b, Nat.mod_lt _ (by have := j.isLt; omega)⟩

end ExactQuantumFactoring.Triangular


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TriangularCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators
open BooleanNetwork

abbrev work (b : ℕ) := 159*b+6
abbrev width (b : ℕ) := (b+b)+(b+b)+work b

noncomputable def encode (b : ℕ) (u : Bits b × ZMod (2^b)) : Basis (width b) :=
  packed (work b) (Fin.append u.1 ((basisResidue b).symm u.2)) (fun _ => false)

def dataWire {b : ℕ} (j : Fin b) : Fin (width b) := ⟨j.val,by have := j.isLt; dsimp [width,work]; omega⟩

noncomputable def rowPerm {b : ℕ} (j : Fin b) : Equiv.Perm (Bits b × ZMod (2^b)) where
  toFun u := (u.1,u.2+(rowShift j u.1 : ZMod (2^b)))
  invFun u := (u.1,u.2-(rowShift j u.1 : ZMod (2^b)))
  left_inv u := by simp
  right_inv u := by simp

end ExactQuantumFactoring.Triangular


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TriangularKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators
open OrderTrial

noncomputable def residuePhase (a : ℕ) (z : ZMod (2^(a+2))) : ℂ :=
  phaseState (2^a) z.val

end ExactQuantumFactoring.Triangular


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TriangularPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators
open BooleanNetwork

def phaseRegister (b : ℕ) : Register b (width b) where
  toFun i := ⟨b+i.val,by dsimp [width,work]; have := i.isLt; omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hh := congrArg Fin.val h
    change b+i.val=b+j.val at hh
    omega

def preparation (a : ℕ) : List (Instruction (width (a+2))) :=
  (preparePhase (a+2) (by omega)).map (Instruction.place (phaseRegister (a+2)))

end ExactQuantumFactoring.Triangular


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderSampleCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Actual modular-power/triangular-transform order sampler. All arithmetic
inputs are read-only wires; the modular output remains coherent. -/
namespace ExactQuantumFactoring.OrderSample
open scoped BigOperators
open BooleanNetwork Triangular

abbrev inputWidth (w b : ℕ) := (w+w)+Triangular.width b

abbrev scratch (w b : ℕ) := w+b*(3672*w*w+436*w+36)
abbrev width (w b : ℕ) := inputWidth w b+w+scratch w b

end ExactQuantumFactoring.OrderSample


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_InitialOrderState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork

namespace Triangular

def dataRegister (b : ℕ) : Register b (width b) :=
  ⟨dataWire,by
    intro i j h
    exact Fin.ext (congrArg (fun t : Fin (width b) => t.val) h)⟩

def uniformPreparation (b : ℕ) : List (Instruction (width b)) :=
  (hadamardPrefix b b le_rfl).map (Instruction.place (dataRegister b))

end Triangular
namespace OrderSample

def initial (w b : ℕ) : List (Instruction (width w b)) :=
  firstProgram w (scratch w b) (rightProgram (w+w) (Triangular.uniformPreparation b))

end OrderSample
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderTrialLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

/-- Unnormalized joint amplitude after modular powering and the selected
phase-transform block. The modular-power register is NOT copied before this
interference sum. -/
noncomputable def selectedSampleAmplitude {G : Type*} [Group G]
    (Q k : ℕ) (a u : G) : ℂ := by
  classical
  exact (Q : ℂ)⁻¹ * ∑ x ∈ Finset.range Q,
    if a^x = u then phase ((k : ℝ)*x/Q) else 0

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderSamplerMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness
namespace OrderTrial

/-- Distinct powers in one period; this is an embedding, not an oracle for r. -/
def powerOrbit {G : Type*} [Group G] (a : G) : Fin (orderOf a)→G := fun t => a^t.val

end OrderTrial
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RecordedHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! The same-history deferred-filter argument of Section 6, at the level of
finite complex amplitudes with all old registers retained.  These are proved
lemmas for the main construction, not assumptions replacing that construction. -/
namespace ExactQuantumFactoring.RecordedHistory
open scoped BigOperators
open ExactQuantumFactoring.Exactness

/-- A fresh controlled computation appends a register, retaining the old one. -/
noncomputable def appendState {H Y : Type*} (ψ : H → ℂ) (fresh : H → Y → ℂ) : H × Y → ℂ :=
  fun hy => ψ hy.1 * fresh hy.1 hy.2

end ExactQuantumFactoring.RecordedHistory


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ParallelPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness

def leftRegister (p q : ℕ) : Register p (p+q) := ⟨Fin.castAdd q,Fin.castAdd_injective p q⟩

def leftProgram {p : ℕ} (q : ℕ) (ops : List (Instruction p)) : List (Instruction (p+q)) :=
  ops.map (Instruction.place (leftRegister p q))

noncomputable def independentState {α β : Type*} (ψ : α→ℂ) (χ : β→ℂ) : α×β→ℂ :=
  fun xy => ψ xy.1*χ xy.2

def parallelProgram {p q : ℕ} (A : List (Instruction p)) (B : List (Instruction q)) :
    List (Instruction (p+q)) := leftProgram q A ++ rightProgram p B

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_IntegerExpressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- Balanced integers avoid a word-size-dependent signed representation. -/
structure IntExpr (v : Type*) where
  pos : NatExpr v
  neg : NatExpr v

namespace IntExpr
variable {v : Type*}

def eval (x : v → ℕ) (e : IntExpr v) : ℤ := (e.pos.eval x : ℤ)-e.neg.eval x

def ofNat (e : NatExpr v) : IntExpr v := ⟨e,.const 0⟩
def ofInt (z : ℤ) : IntExpr v := ⟨.const z.toNat,.const (-z).toNat⟩
def add (a b : IntExpr v) : IntExpr v := ⟨.add a.pos b.pos,.add a.neg b.neg⟩
def negation (a : IntExpr v) : IntExpr v := ⟨a.neg,a.pos⟩
def sub (a b : IntExpr v) : IntExpr v := add a (negation b)
def mul (a b : IntExpr v) : IntExpr v :=
  ⟨.add (.mul a.pos b.pos) (.mul a.neg b.neg),
   .add (.mul a.neg b.pos) (.mul a.pos b.neg)⟩
def scale (a : IntExpr v) (b : NatExpr v) : IntExpr v := mul a (ofNat b)
def toNat (a : IntExpr v) : NatExpr v := .sub a.pos a.neg
def natAbs (a : IntExpr v) : NatExpr v := .add (.sub a.pos a.neg) (.sub a.neg a.pos)
def iteLe (a b : NatExpr v) (c d : IntExpr v) : IntExpr v :=
  ⟨.iteLe a b c.pos d.pos,.iteLe a b c.neg d.neg⟩

@[simp] lemma eval_ofNat (x : v → ℕ) (e : NatExpr v) : (ofNat e).eval x=(e.eval x : ℤ) := by
  simp [ofNat,eval,NatExpr.eval]
@[simp] lemma eval_ofInt (x : v → ℕ) (z : ℤ) : (ofInt z : IntExpr v).eval x=z := by
  simp [ofInt,eval,NatExpr.eval]
@[simp] lemma eval_add (x : v → ℕ) (a b : IntExpr v) : (add a b).eval x=a.eval x+b.eval x := by
  simp [add,eval,NatExpr.eval]
  ring
@[simp] lemma eval_negation (x : v → ℕ) (a : IntExpr v) : (negation a).eval x= -a.eval x := by
  simp [negation,eval]
@[simp] lemma eval_sub (x : v → ℕ) (a b : IntExpr v) : (sub a b).eval x=a.eval x-b.eval x := by
  simp [sub,sub_eq_add_neg]
@[simp] lemma eval_mul (x : v → ℕ) (a b : IntExpr v) : (mul a b).eval x=a.eval x*b.eval x := by
  simp [mul,eval,NatExpr.eval]
  ring
@[simp] lemma eval_scale (x : v → ℕ) (a : IntExpr v) (b : NatExpr v) :
    (scale a b).eval x=a.eval x*b.eval x := by simp [scale]
@[simp] lemma eval_toNat (x : v → ℕ) (a : IntExpr v) : (toNat a).eval x=(a.eval x).toNat := by
  simp [toNat,NatExpr.eval,eval]
@[simp] lemma eval_natAbs (x : v → ℕ) (a : IntExpr v) : (natAbs a).eval x=(a.eval x).natAbs := by
  simp only [natAbs,NatExpr.eval,eval]
  omega
@[simp] lemma eval_iteLe (x : v → ℕ) (a b : NatExpr v) (c d : IntExpr v) :
    (iteLe a b c d).eval x = if a.eval x ≤ b.eval x then c.eval x else d.eval x := by
  simp only [iteLe,eval,NatExpr.eval]
  split_ifs <;> rfl

end IntExpr
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RationalExpressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring

/-- Rational arithmetic as fixed finite syntax over nonnegative registers. No
canonical-fraction reduction or unit-cost large-integer operation is required. -/
structure RatExpr (v : Type*) where
  num : IntExpr v
  den : NatExpr v

namespace RatExpr
variable {v : Type*}

def eval (x : v → ℕ) (a : RatExpr v) : ℚ := (a.num.eval x : ℚ)/(a.den.eval x : ℚ)
def ofNat (a : NatExpr v) : RatExpr v := ⟨IntExpr.ofNat a,.const 1⟩
def ofInt (a : IntExpr v) : RatExpr v := ⟨a,.const 1⟩
def const (a : ℚ) : RatExpr v := ⟨IntExpr.ofInt a.num,.const a.den⟩
def normalize (a : RatExpr v) : RatExpr v :=
  ⟨IntExpr.iteLe a.den (.const 0) (IntExpr.ofInt 0) a.num,
   .iteLe a.den (.const 0) (.const 1) a.den⟩
def add (a b : RatExpr v) : RatExpr v :=
  let a := normalize a
  let b := normalize b
  ⟨IntExpr.add (a.num.scale b.den) (b.num.scale a.den),.mul a.den b.den⟩
def negation (a : RatExpr v) : RatExpr v := ⟨a.num.negation,a.den⟩
def sub (a b : RatExpr v) : RatExpr v := add a b.negation
def mul (a b : RatExpr v) : RatExpr v := ⟨a.num.mul b.num,.mul a.den b.den⟩
def inverse (a : RatExpr v) : RatExpr v :=
  ⟨a.num.scale a.den,.mul a.num.natAbs a.num.natAbs⟩
def div (a b : RatExpr v) : RatExpr v := mul a b.inverse
def pow (a : RatExpr v) : ℕ → RatExpr v
  | 0 => const 1
  | n+1 => mul (pow a n) a

@[simp] lemma eval_ofNat (x : v → ℕ) (a : NatExpr v) : (ofNat a).eval x=a.eval x := by
  simp [ofNat,eval,NatExpr.eval]
@[simp] lemma eval_ofInt (x : v → ℕ) (a : IntExpr v) : (ofInt a).eval x=a.eval x := by
  simp [ofInt,eval,NatExpr.eval]
@[simp] lemma eval_const (x : v → ℕ) (a : ℚ) : (const a : RatExpr v).eval x=a := by
  simp [const,eval,NatExpr.eval,Rat.num_div_den]
@[simp] lemma eval_normalize (x : v → ℕ) (a : RatExpr v) : a.normalize.eval x=a.eval x := by
  by_cases h : a.den.eval x=0
  · simp [normalize,eval,NatExpr.eval,h]
  · have hp : ¬a.den.eval x ≤ 0 := by omega
    simp [normalize,eval,NatExpr.eval,hp]
@[simp] lemma eval_negation (x : v → ℕ) (a : RatExpr v) : a.negation.eval x= -a.eval x := by
  simp [negation,eval,neg_div]
@[simp] lemma eval_mul (x : v → ℕ) (a b : RatExpr v) : (mul a b).eval x=a.eval x*b.eval x := by
  simp [mul,eval,NatExpr.eval,div_mul_div_comm]
@[simp] lemma eval_inverse (x : v → ℕ) (a : RatExpr v) : a.inverse.eval x=(a.eval x)⁻¹ := by
  simp only [inverse,eval,IntExpr.eval_scale,IntExpr.eval_natAbs,NatExpr.eval,
    Int.cast_mul,Int.cast_natCast,Nat.cast_mul,inv_div]
  have hsq : ((a.num.eval x).natAbs : ℚ)*((a.num.eval x).natAbs : ℚ) =
      (a.num.eval x : ℚ)*(a.num.eval x : ℚ) := by
    rw [← sq,← sq]
    have h : ((a.num.eval x).natAbs : ℤ)^2=(a.num.eval x)^2 := by
      rw [Int.natCast_natAbs,sq_abs]
    simpa only [Int.cast_pow,Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) h
  rw [hsq]
  by_cases hz : (a.num.eval x : ℚ)=0
  · simp [hz]
  · field_simp
@[simp] lemma eval_div (x : v → ℕ) (a b : RatExpr v) : (div a b).eval x=a.eval x/b.eval x := by
  simp [div,div_eq_mul_inv]
@[simp] lemma eval_pow (x : v → ℕ) (a : RatExpr v) (n : ℕ) : (pow a n).eval x=(a.eval x)^n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp [pow,ih,pow_succ]

end RatExpr
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PolynomialExpressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace RatExpr
variable {v : Type*}
def sum (f : ℕ → RatExpr v) : ℕ → RatExpr v
  | 0 => const 0
  | n+1 => add (sum f n) (f n)
end RatExpr

/-- Bounded polynomial arithmetic is itself finite rational syntax. -/
inductive PolyExpr (v : Type*) where
  | C : RatExpr v → PolyExpr v
  | X : PolyExpr v
  | add : PolyExpr v → PolyExpr v → PolyExpr v
  | negation : PolyExpr v → PolyExpr v
  | mul : PolyExpr v → PolyExpr v → PolyExpr v

namespace PolyExpr
variable {v : Type*}
open Polynomial
noncomputable def eval (x : v → ℕ) : PolyExpr v → ℚ[X]
  | .C c => Polynomial.C (c.eval x)
  | .X => Polynomial.X
  | .add a b => a.eval x+b.eval x
  | .negation a => -a.eval x
  | .mul a b => a.eval x*b.eval x

def coeff : PolyExpr v → ℕ → RatExpr v
  | .C c,k => if k=0 then c else RatExpr.const 0
  | .X,k => if k=1 then RatExpr.const 1 else RatExpr.const 0
  | .add a b,k => RatExpr.add (a.coeff k) (b.coeff k)
  | .negation a,k => (a.coeff k).negation
  | .mul a b,k => RatExpr.sum (fun i => RatExpr.mul (a.coeff i) (b.coeff (k-i))) (k+1)

def sub (a b : PolyExpr v) : PolyExpr v := add a b.negation
def const (r : ℚ) : PolyExpr v := .C (RatExpr.const r)
def pow (a : PolyExpr v) : ℕ → PolyExpr v
  | 0 => const 1
  | n+1 => mul (pow a n) a

def comp : PolyExpr v → PolyExpr v → PolyExpr v
  | .C c,_ => .C c
  | .X,b => b
  | .add a c,b => .add (comp a b) (comp c b)
  | .negation a,b => .negation (comp a b)
  | .mul a c,b => .mul (comp a b) (comp c b)

@[simp] lemma eval_const (x : v → ℕ) (r : ℚ) : (const r : PolyExpr v).eval x=Polynomial.C r := by
  simp [const,eval]
@[simp] lemma eval_sub (x : v → ℕ) (a b : PolyExpr v) : (sub a b).eval x=a.eval x-b.eval x := by
  simp [sub,eval,sub_eq_add_neg]
@[simp] lemma eval_pow (x : v → ℕ) (a : PolyExpr v) (n : ℕ) : (pow a n).eval x=(a.eval x)^n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp [pow,eval,ih,pow_succ]
@[simp] lemma eval_comp (x : v → ℕ) (a b : PolyExpr v) : (comp a b).eval x=(a.eval x).comp (b.eval x) := by
  induction a with
  | C c => simp [comp,eval]
  | X => simp [comp,eval]
  | add a c ia ic => simp [comp,eval,ia,ic,Polynomial.add_comp]
  | negation a ia => simp [comp,eval,ia,Polynomial.neg_comp]
  | mul a c ia ic => simp [comp,eval,ia,ic,Polynomial.mul_comp]
end PolyExpr
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FilterExpressionSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace RatExpr
variable {v : Type*}
instance instOfNat (n : ℕ) : OfNat (RatExpr v) n := ⟨const n⟩
instance instAdd : Add (RatExpr v) := ⟨add⟩
instance instMul : Mul (RatExpr v) := ⟨mul⟩
instance instSub : Sub (RatExpr v) := ⟨sub⟩
instance instDiv : Div (RatExpr v) := ⟨div⟩
instance instNeg : Neg (RatExpr v) := ⟨negation⟩
instance instInv : Inv (RatExpr v) := ⟨inverse⟩
instance instPowNat : Pow (RatExpr v) ℕ := ⟨pow⟩
@[simp] lemma eval_num (x : v → ℕ) (n : ℕ) : (no_index (OfNat.ofNat n : RatExpr v)).eval x=n := eval_const x n
@[simp] lemma eval_times (x : v → ℕ) (a b : RatExpr v) : (a*b).eval x=a.eval x*b.eval x := eval_mul x a b
@[simp] lemma eval_over (x : v → ℕ) (a b : RatExpr v) : (a/b).eval x=a.eval x/b.eval x := eval_div x a b
@[simp] lemma eval_neg (x : v → ℕ) (a : RatExpr v) : (-a).eval x= -a.eval x := eval_negation x a
@[simp] lemma eval_inv (x : v → ℕ) (a : RatExpr v) : (a⁻¹).eval x=(a.eval x)⁻¹ := eval_inverse x a
@[simp] lemma eval_power (x : v → ℕ) (a : RatExpr v) (n : ℕ) : (a^n).eval x=(a.eval x)^n := eval_pow x a n
end RatExpr
namespace PolyExpr
variable {v : Type*}
instance instOfNat (n : ℕ) : OfNat (PolyExpr v) n := ⟨const n⟩
instance instAdd : Add (PolyExpr v) := ⟨add⟩
instance instMul : Mul (PolyExpr v) := ⟨mul⟩
instance instSub : Sub (PolyExpr v) := ⟨sub⟩
instance instNeg : Neg (PolyExpr v) := ⟨negation⟩
instance instPowNat : Pow (PolyExpr v) ℕ := ⟨pow⟩
@[simp] lemma eval_num (x : v → ℕ) (n : ℕ) : (no_index (OfNat.ofNat n : PolyExpr v)).eval x=Polynomial.C (n : ℚ) := eval_const x n
@[simp] lemma eval_plus (x : v → ℕ) (a b : PolyExpr v) : (a+b).eval x=a.eval x+b.eval x := rfl
@[simp] lemma eval_times (x : v → ℕ) (a b : PolyExpr v) : (a*b).eval x=a.eval x*b.eval x := rfl
@[simp] lemma eval_minus (x : v → ℕ) (a b : PolyExpr v) : (a-b).eval x=a.eval x-b.eval x := eval_sub x a b
@[simp] lemma eval_neg (x : v → ℕ) (a : PolyExpr v) : (-a).eval x= -a.eval x := rfl
@[simp] lemma eval_power (x : v → ℕ) (a : PolyExpr v) (n : ℕ) : (a^n).eval x=(a.eval x)^n := eval_pow x a n
end PolyExpr
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RationalRounding
attribute [-instance] _root_.OAI.ExactQuantumFactoring.RatExpr.instAdd _root_.OAI.ExactQuantumFactoring.RatExpr.instDiv _root_.OAI.ExactQuantumFactoring.RatExpr.instInv _root_.OAI.ExactQuantumFactoring.RatExpr.instMul _root_.OAI.ExactQuantumFactoring.RatExpr.instNeg _root_.OAI.ExactQuantumFactoring.RatExpr.instOfNat _root_.OAI.ExactQuantumFactoring.RatExpr.instPowNat _root_.OAI.ExactQuantumFactoring.RatExpr.instSub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace IntExpr
variable {v : Type*}

def ceilRatioNat (a : IntExpr v) (b : NatExpr v) : NatExpr v :=
  .div (.sub (.add a.toNat b) (.const 1)) b

def floorRatio (a : IntExpr v) (b : NatExpr v) : IntExpr v :=
  sub (ofNat (.div a.toNat b)) (ofNat (ceilRatioNat a.negation b))

end IntExpr

namespace RatExpr
variable {v : Type*}
def ceilNat (a : RatExpr v) : NatExpr v := a.num.ceilRatioNat a.den
def floor (a : RatExpr v) : IntExpr v := a.num.floorRatio a.den
def ceil (a : RatExpr v) : IntExpr v := a.negation.floor.negation
end RatExpr
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetentionDenominators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Explicit, uniform O(n) fair-bit lengths for every order-trial retention.
Mere dyadicity would not bound the worst-case circuit cost. -/
namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

def DyadicAt (k : ℕ) (x : ℚ) : Prop := ∃ z : ℤ, x=(z:ℚ)/2^k

noncomputable def discrepancyRetention (n d j t : ℕ) : ℚ :=
  2*((2:ℚ)^n)^3*(majorant ((2^n)^16) (2^n) d j ((j*t)%d)-
    residueProbabilityRat ((2^n)^16) d j t)*modeCoeff n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j)
noncomputable def remainderRetention (n d j : ℕ) : ℚ :=
  4*((2:ℚ)^n)^2*modeRemainder n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j)

/-- One clock-independent number of bits works for all three modes, on every
valid label, including d=1,j=0. -/
def retentionBits (n : ℕ) := 80*n+20

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ThresholdRetention
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Exact threshold thinning by a FIXED (not rejection-sampled) block of fair
bits. The complete block is retained in the physical history. -/
namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness BooleanNetwork BitArithmetic

/-- The natural floor implementation of the exact dyadic acceptance threshold. -/
def thresholdExpr {v : Type*} (T : ℕ) (p : RatExpr v) (coin : NatExpr v) : NatExpr v :=
  .iteLe (.add coin (.const 1)) ((p*RatExpr.ofNat (.const (2^T))).floor.toNat)
    (.const 1) (.const 0)

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TrialRetentionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial

noncomputable def firstRetention (n d j : ℕ) : ℚ :=
  modeCoeff n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j)

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TrialRawPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness

namespace OrderTrial

abbrev guessWidth (n : ℕ) := n+(n+(n+retentionBits n))
def guessProgram (n : ℕ) : List (Instruction (guessWidth n)) :=
  parallelProgram (hadamardPrefix n n le_rfl) (parallelProgram (hadamardPrefix n n le_rfl)
    (parallelProgram (hadamardPrefix n n le_rfl) (hadamardPrefix (retentionBits n) (retentionBits n) le_rfl)))
abbrev rawWidth (w s n : ℕ) := 2+(OrderSample.width w (s+2)+guessWidth n)

end OrderTrial
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_DyadicCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness OrderTrial

namespace Completion

def coeff (W t : ℕ) (s z : ℚ) : ℚ := completionCoeff (W+t+2) z ((1-1/(2:ℚ)^t)*s)
def guessRetention (W t : ℕ) (s z : ℚ) : ℚ :=
  completionRemainder (W+t+2) z ((1-1/(2:ℚ)^t)*s)*(2:ℚ)^W/(1/(2:ℚ)^t)
def coinBits (W t d : ℕ) : ℕ := (W+t+2)+t+d

/-- Literal fixed-gate program for the raw extended record; no oracle for the
future data, success probability, or distinguished guess occurs in its code. -/
def program {q : ℕ} (P : List (Instruction q)) (W t d : ℕ) :
    List (Instruction (t+(q+(W+coinBits W t d)))) :=
  parallelProgram (hadamardPrefix t t le_rfl) (parallelProgram P
    (parallelProgram (hadamardPrefix W W le_rfl) (hadamardPrefix (coinBits W t d) (coinBits W t d) le_rfl)))

end Completion
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_LabelRecoveryCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

/-- A bounded scan; either the sole valid label, or the distinguished zero pair. -/
def scanPairs (Q B k : ℕ) : ℕ → ℕ×ℕ
  | 0 => (0,0)
  | i+1 => let a := checkedPair Q B k i
           if a.1≠0 then a else scanPairs Q B k i

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderCandidateLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness

namespace OrderTrial

def ValidLabel (n a m d j : ℕ) : Prop :=
  0<d ∧ d<2^n ∧ j<d ∧ Nat.Coprime j d ∧ a^d%m=1

end OrderTrial
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators
open Exactness RepeatedTrials

def minOption : Option ℕ→Option ℕ→Option ℕ
  | none,b => b
  | some a,none => some a
  | some a,some b => some (min a b)

def minimumCandidate : List (Option ℕ)→Option ℕ
  | [] => none
  | a::as => minOption a (minimumCandidate as)

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TransitionEqualization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials OrderTrial

namespace Completion

def target (n : ℕ) : ℚ := 1-1/(2:ℚ)^n
def transitionWidth (n : ℕ) : ℕ := n*(n^5+1)
def listSuccess (m n K : ℕ) : ℚ :=
  1-(1-(favorableCount m n : ℚ)/(2:ℚ)^(Nat.clog 2 m))^K
def orderSuccess (d K : ℕ) : ℚ :=
  1-(1-(Nat.totient d:ℚ)*prescribedMass d)^K

end Completion
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetrospectiveStatistics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open AuxiliaryTree

/-- The closed statistics are evaluated over the supplied exponent record,
not by enumerating residues or invoking a factorization oracle. -/
noncomputable def recordPhi (f : FactorRecord) : ℕ :=
  ∏ p∈f.support, primePowerUnitCount p (f p)

noncomputable def recordFavorable (n : ℕ) (f : FactorRecord) : ℕ :=
  recordPhi f - ∑ t : Fin (n+1), ∏ p∈f.support,
    closedLevelCount (primePowerUnitCount p (f p)) t.val

noncomputable def dataRecord (data : FactorData) (m : ℕ) : FactorRecord :=
  primeRecord (dataDivisorPrimes data m)

noncomputable def dataPhi (data : FactorData) (m : ℕ) : ℕ := recordPhi (dataRecord data m)
noncomputable def dataFavorable (data : FactorData) (m n : ℕ) : ℕ := recordFavorable n (dataRecord data m)

/-- Literal prime stripping in natural modular arithmetic. This is exactly the
scan compiled by `stripScan`; its inputs come only from the supplied data. -/
def stripFactorsNat (a m : ℕ) : List ℕ→ℕ→ℕ
  | [], v => v
  | q::qs, v => stripFactorsNat a m qs (stripPrimeNat a m q v)

noncomputable def dataOrder (data : FactorData) (a m : ℕ) : ℕ :=
  stripFactorsNat a m (dataTotientPrimes data m) (dataPhi data m)

noncomputable def dataListSuccess (data : FactorData) (m n K : ℕ) : ℚ :=
  1-(1-(dataFavorable data m n : ℚ)/(2:ℚ)^(Nat.clog 2 m))^K
noncomputable def dataOrderSuccess (data : FactorData) (a m K : ℕ) : ℚ :=
  Completion.orderSuccess (dataOrder data a m) K

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ProductStates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness

/-- Independent, not necessarily identically distributed, retained registers. -/
noncomputable def productState {ι : Type*} [Fintype ι] {α : ι → Type*}
    (ψ : ∀ i, α i → ℂ) (x : ∀ i, α i) : ℂ := ∏ i, ψ i (x i)

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CompletedOrderSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials OrderTrial

namespace OrderSlots

abbrev sampleExponent (n : ℕ) := 16*n-2

end OrderSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactorController
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Bounded, guarded binary factor controller for a single auxiliary-tree node.
Only proper divisors are accepted and primality is tested, never assumed.  The
mathematical prime-factor count is used solely in its termination proof. -/
namespace ExactQuantumFactoring.FactorController
open AuxiliaryTree

def ProperDivisor (m d : ℕ) : Prop := 1 < d ∧ d < m ∧ d ∣ m
instance instDecidableProperDivisor (m d : ℕ) : Decidable (ProperDivisor m d) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def weight (ms : List ℕ) : ℕ := (ms.map (fun m =>  2*splitWeight m-1)).sum

end ExactQuantumFactoring.FactorController


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FavorableSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

/-- The distinguished CRT residue used in the list-completion branch. The
parameter p₀ is subsequently chosen as the least prime component. -/
noncomputable def canonicalUnit {m : ℕ} (hm : m≠0) (p₀ : Component m) : (ZMod m)ˣ :=
  (unitCRT m hm).symm (fun p => if p=p₀ then 1 else -1)

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ProvidedSplits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open FactorController

/-- A guarded scan. Invalid proposals never change the arithmetic product
invariant of the factoring controller. -/
def firstProper (m : ℕ) : List ℕ→ℕ
  | [] => 0
  | d::ds => if ProperDivisor m d then d else firstProper m ds

def orderSplit (m : ℕ) (ars : List (ℕ×ℕ)) : ℕ :=
  firstProper m (ars.map (fun ar => candidateDivisor m ar.1 ar.2))

/-- Root searches are clocked by the ORIGINAL input length n. -/
def rootProposals (m n : ℕ) : List ℕ :=
  (List.range (n+1)).map (fun e => Primality.boundedRoot m e n)

def rootSplit (m n : ℕ) : ℕ := firstProper m (rootProposals m n)

def suppliedDivisor (m n : ℕ) (ars : List (ℕ×ℕ)) : ℕ :=
  if 2∣m then 2 else
  if ProperDivisor m (rootSplit m n) then rootSplit m n else orderSplit m ars

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhaseOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork

namespace BooleanNetwork

def phaseTarget {n r : ℕ} : Fin (n+1+r) := ⟨n,by omega⟩

end BooleanNetwork
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalAmplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness

/-- A support invariant for a read-only classical input sector. -/
def Supported {ι : Type*} (S : ι → Prop) (v : ι → ℂ) : Prop :=
  ∀ x, ¬ S x → v x = 0

/-- Matrix entries cannot change the read-only input. -/
def RespectsSector {ι : Type*} (S : ι → Prop) (U : Matrix ι ι ℂ) : Prop :=
  ∀ x y, ¬ (S x ↔ S y) → U x y = 0

noncomputable def signState {ι : Type*} (p : ι → Bool) (v : ι → ℂ) : ι → ℂ :=
  fun x => (if p x then (-1:ℂ) else 1)*v x

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ReadOnlyCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

lemma Gate.arity_pos (g : Gate) : 0<g.arity := by
  cases g with
  | mk p inv ctrl => cases p <;> cases ctrl <;> simp [Gate.arity,Primitive.arity]

def Instruction.target {q : ℕ} (o : Instruction q) : Fin q :=
  o.wire ⟨o.gate.arity-1,by have := o.gate.arity_pos; omega⟩


end ExactQuantumFactoring
end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ControlledHadamard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

/-- One of the literal fixed alphabet gates; the extra control is the first
wire and is never modified. -/
abbrev controlledHadamardAt {q : ℕ} (c t : Fin q) (h : c≠t) : Instruction q :=
  ⟨⟨.hadamard,false,true⟩, ![c,t], by
    change Function.Injective (![c,t] : Fin 2→Fin q)
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all⟩

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_MaskedPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness BitArithmetic BooleanNetwork

def maskGate (n : ℕ) (j : Fin n) : Instruction (n+n) :=
  controlledHadamardAt (j.castAdd n) (Fin.natAdd n j) (by
    intro hh
    have he := congrArg Fin.val hh
    simp only [Fin.val_castAdd,Fin.val_natAdd] at he
    have := j.isLt
    omega)

def maskedPrefix (n : ℕ) : (k : ℕ)→k ≤ n→List (Instruction (n+n))
  | 0,_ => []
  | k+1,h => maskedPrefix n k (by omega)++[maskGate n ⟨k,by omega⟩]

def selectedPrefix {n : ℕ} (mask : Basis n) : (k : ℕ)→k ≤ n→List (Instruction n)
  | 0,_ => []
  | k+1,h => selectedPrefix mask k (by omega)++
      (if mask ⟨k,by omega⟩ then [hadamardAt ⟨k,by omega⟩] else [])

def prefixMask (n b : ℕ) : Basis n := fun i => decide (i.val<b)

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TransitionWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials

namespace ListSlots

abbrev K (n : ℕ) := n^5

end ListSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ListSamplerCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.ListSampler
open Exactness BitArithmetic BooleanNetwork

abbrev work (n : ℕ) := n*(49*n+8)
abbrev width (n : ℕ) := n+n+(n+work n)

def maskRegister (n : ℕ) : Register (n+n) (width n) where
  toFun i := ⟨n+i.val,by have := i.isLt; dsimp [width]; omega⟩
  inj' := by
    intro i j hh
    apply Fin.ext
    have h := congrArg Fin.val hh
    dsimp at h
    omega

end ExactQuantumFactoring.ListSampler


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TensorPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials

abbrev tensorWidth (q : ℕ) : ℕ→ℕ
  | 0 => 0
  | K+1 => q+tensorWidth q K

def tensorProgram {q : ℕ} (ops : List (Instruction q)) : (K : ℕ)→List (Instruction (tensorWidth q K))
  | 0 => []
  | K+1 => parallelProgram ops (tensorProgram ops K)

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalListSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials
namespace PhysicalListSlots

abbrev ordinaryWidth (n : ℕ) := tensorWidth (ListSampler.width n) (n^5)

abbrev width (n : ℕ) := 2*n+(ordinaryWidth n+(Completion.transitionWidth n+
  Completion.coinBits (Completion.transitionWidth n) (2*n) (n*n^5)))

end PhysicalListSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_UniversalSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials OrderTrial
namespace UniversalSplit

def Hard (m : ℕ) : Prop := 2 ≤ m ∧ ¬m.Prime ∧ Odd m ∧ ¬Primality.PerfectPower m

/-- Source's distinguished component: the least prime divisor, not an arbitrary
component for which the compiler would need extra advice. -/
def firstComponent {m : ℕ} (hm : 2 ≤ m) : Component m :=
  ⟨m.minFac,Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega),Nat.minFac_dvd m,by omega⟩⟩

end UniversalSplit
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetrospectiveResidues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open AuxiliaryTree

/-- The distinguished component is selected from the supplied record, not by
factoring the requested integer a second time. -/
def recordFirst (f : FactorRecord) : ℕ :=
  if h : f.support.Nonempty then f.support.min' h else 0

noncomputable def dataResidueGood (data : FactorData) (a m : ℕ) : Prop :=
  a < m ∧ Nat.Coprime a m ∧
    ¬∀ p∈(dataRecord data m).support,
      padicValNat 2 (dataOrder data a (p^(dataRecord data m) p))=
      padicValNat 2 (dataOrder data a
        ((recordFirst (dataRecord data m))^((dataRecord data m) (recordFirst (dataRecord data m)))))

/-- Checking the uniquely specified CRT residue needs only congruences against
the supplied prime powers; no CRT search is hidden in the guess validator. -/
noncomputable def dataCanonicalResidue (data : FactorData) (a m : ℕ) : Prop :=
  a < m ∧ ∀ p∈(dataRecord data m).support,
    a%(p^(dataRecord data m) p)=
      if p=recordFirst (dataRecord data m) then 1 else p^(dataRecord data m) p-1

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TraceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

namespace AuxiliaryTree

def visits : ℕ→ℕ→List ℕ
  | 0, _ => []
  | depth+1, m => m::(children m).flatMap (visits depth)

end AuxiliaryTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OccurrenceQueue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.AuxiliaryTree

/-- The full occurrence preorder; equal labels under different parents are
retained as different list elements. This is only a correctness invariant,
never used as the modulus-input physical circuit's initializer. -/
def preorder (m : ℕ) : List ℕ :=
  m::((children m).attach.flatMap (fun d=>preorder d.val))
termination_by m
decreasing_by exact (child_bounds d.property).2

def forest (xs : List ℕ) : List ℕ := xs.flatMap preorder

def advance : List ℕ→List ℕ
  | []=>[]
  | m::ms=>children m++ms

def run : ℕ→List ℕ→List ℕ
  | 0,xs=>xs
  | t+1,xs=>run t (advance xs)

end ExactQuantumFactoring.AuxiliaryTree


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_QueueCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.AuxiliaryTree

/-- Chronological node heads, in reverse recording order. Zero denotes a dummy
slot after the pending queue has become empty. Duplicate occurrences remain. -/
def seen (xs : List ℕ) : ℕ→List ℕ
  | 0=>[]
  | t+1=>(run t xs).headD 0::seen xs t

end ExactQuantumFactoring.AuxiliaryTree


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PreparedOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness

def targetRegister (n m r : ℕ) : Register m (n+m+r) where
  toFun i := ⟨n+i.val,by omega⟩
  inj' := by
    intro i j hh
    apply Fin.ext
    have h := congrArg Fin.val hh
    change n+i.val=n+j.val at h
    omega

def targetProgram {m : ℕ} (n r : ℕ) (ops : List (Instruction m)) :
    List (Instruction (n+m+r)) := ops.map (Instruction.place (targetRegister n m r))

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalCompletionOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace Completion

abbrev totalWidth (q W t d : ℕ) := t+(q+(W+coinBits W t d))

end Completion
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TensorWiring
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork

def tensorWire (q : ℕ) : (K : ℕ) → Fin K → Fin q → Fin (tensorWidth q K)
  | 0, i => Fin.elim0 i
  | K+1, i => Fin.cases (fun j => j.castAdd (tensorWidth q K))
      (fun i j => Fin.natAdd q (tensorWire q K i j)) i

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalOrderSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open Exactness RepeatedTrials OrderTrial
namespace OrderSlots

abbrev ordinaryWidth (n : ℕ) := tensorWidth (rawWidth n (sampleExponent n) n) (n^5)
abbrev coinWidth (n : ℕ) := Completion.coinBits (Completion.transitionWidth n) (2*n) ((n+10)*n^5)
abbrev width (n : ℕ) := 2*n+(ordinaryWidth n+(Completion.transitionWidth n+coinWidth n))

end OrderSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness
namespace FixedSplit

abbrev ordersWidth (n : ℕ) := tensorWidth (OrderSlots.width n) (n^5)

end FixedSplit
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeControlCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork FactorController

namespace NodeCircuit

abbrev width (s w : ℕ) := (s+1)*w+w

end NodeCircuit
end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeStateCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork FactorController
namespace NodeStateCircuit

abbrev width (s w : ℕ) := ((s+1)*w+(s+1)*w)+1
abbrev inWidth (s w : ℕ) := width s w+w

end NodeStateCircuit
end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_MinimumCandidateCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

def minNonzero (a b : ℕ) : ℕ := if a=0 then b else if b=0 then a else min a b

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RawTrialLabelCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

abbrev decodeSteps (s : ℕ) := 2*(s+3)+1
abbrev decodeWidth (u s n : ℕ) := cfWidth (s+3) (decodeSteps s)+u+n+retentionBits n+(s+3)+3

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ProgressionEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


/-! Constant-length exact evaluation of the selected arithmetic progression.
The exponentially many progression points are replaced by seven truncated
arithmetic sums. This is the explicit arithmetic behind source Lemma 4.1. -/
namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

/-- Five fixed terms, of which only the constant and linear ones are nonzero. -/
def linearSum (a b : ℚ) (lo hi : ℕ) : ℚ :=
  fiveTermSum (fun q => if q=0 then a else if q=1 then b else 0) lo hi

/-- A ramp can change sign only once along an arithmetic progression. -/
def rampSum (a b : ℚ) (M : ℕ) : ℚ :=
  if 0 < b then linearSum a b (Int.ceil (-a/b)).toNat M
  else if b < 0 then linearSum a b 0 (min M (Int.ceil (-a/b)).toNat)
  else M*max 0 a

/-- The real coordinate of the seven-ramp spline derivative summed exactly. -/
def phaseSumRe (a b : ℚ) (M : ℕ) : ℚ :=
  -(M:ℚ)+4*linearSum (a+1/2) b 0 M-8*rampSum a b M+
    8*rampSum (a-1/2) b M-8*rampSum (a-1) b M

def phaseSumIm (a b : ℚ) (M : ℕ) : ℚ :=
  4*linearSum (a+1/2) b 0 M-8*rampSum (a+1/4) b M+
    8*rampSum (a-1/4) b M-8*rampSum (a-3/4) b M+
    8*rampSum (a-5/4) b M

/-- Offset and slope are rational values of polynomial bit length, evaluated
using the arithmetic nearest-bin rule rather than any transcendental oracle. -/
def sampleOffset (Q d j t : ℕ) : ℚ :=
  (((j*t)%d:ℕ):ℚ)/d+binErrorRat Q d j*t/Q

def sampleSlope (Q d j : ℕ) : ℚ := binErrorRat Q d j*d/Q

/-- Constant-piece rational P: seven ramp sums, hence no loop of length Q or d. -/
def fastResidueProbability (Q d j t : ℕ) : ℚ :=
  let a := sampleOffset Q d j t
  let b := sampleSlope Q d j
  let M := sampleCount Q d t
  (phaseSumRe a b M ^ 2 + phaseSumIm a b M ^ 2)/(Q:ℚ)^2

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RationalConditionals
attribute [-instance] _root_.OAI.ExactQuantumFactoring.RatExpr.instAdd _root_.OAI.ExactQuantumFactoring.RatExpr.instDiv _root_.OAI.ExactQuantumFactoring.RatExpr.instInv _root_.OAI.ExactQuantumFactoring.RatExpr.instMul _root_.OAI.ExactQuantumFactoring.RatExpr.instNeg _root_.OAI.ExactQuantumFactoring.RatExpr.instOfNat _root_.OAI.ExactQuantumFactoring.RatExpr.instPowNat _root_.OAI.ExactQuantumFactoring.RatExpr.instSub
attribute [-simp] _root_.OAI.ExactQuantumFactoring.RatExpr.eval_inv _root_.OAI.ExactQuantumFactoring.RatExpr.eval_neg _root_.OAI.ExactQuantumFactoring.RatExpr.eval_num _root_.OAI.ExactQuantumFactoring.RatExpr.eval_over _root_.OAI.ExactQuantumFactoring.RatExpr.eval_power _root_.OAI.ExactQuantumFactoring.RatExpr.eval_times
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace IntExpr
variable {v : Type*}

def ifLe (a b c d : IntExpr v) : IntExpr v :=
  iteLe (.add a.pos b.neg) (.add b.pos a.neg) c d
@[simp] lemma eval_ifLe (x : v → ℕ) (a b c d : IntExpr v) :
    (ifLe a b c d).eval x = if a.eval x ≤ b.eval x then c.eval x else d.eval x := by
  simp only [ifLe,eval_iteLe,NatExpr.eval]
  have he : a.pos.eval x+b.neg.eval x ≤ b.pos.eval x+a.neg.eval x ↔ a.eval x ≤ b.eval x := by
    simp only [eval]
    omega
  simp only [he]
end IntExpr

namespace RatExpr
variable {v : Type*}

def ifNatLe (a b : NatExpr v) (c d : RatExpr v) : RatExpr v :=
  ⟨IntExpr.iteLe a b c.num d.num,.iteLe a b c.den d.den⟩
@[simp] lemma eval_ifNatLe (x : v → ℕ) (a b : NatExpr v) (c d : RatExpr v) :
    (ifNatLe a b c d).eval x = if a.eval x ≤ b.eval x then c.eval x else d.eval x := by
  by_cases h : a.eval x ≤ b.eval x
  · simp [ifNatLe,eval,NatExpr.eval,h]
  · simp [ifNatLe,eval,NatExpr.eval,h]

def ifIntLe (a b : IntExpr v) (c d : RatExpr v) : RatExpr v :=
  ifNatLe (.add a.pos b.neg) (.add b.pos a.neg) c d
@[simp] lemma eval_ifIntLe (x : v → ℕ) (a b : IntExpr v) (c d : RatExpr v) :
    (ifIntLe a b c d).eval x = if a.eval x ≤ b.eval x then c.eval x else d.eval x := by
  rw [ifIntLe,eval_ifNatLe]
  simp only [NatExpr.eval]
  have hh : a.pos.eval x+b.neg.eval x ≤ b.pos.eval x+a.neg.eval x ↔ a.eval x ≤ b.eval x := by
    simp only [IntExpr.eval]
    omega
  simp only [hh]

def ifLe (a b c d : RatExpr v) : RatExpr v :=
  let a := a.normalize
  let b := b.normalize
  ifIntLe (a.num.scale b.den) (b.num.scale a.den) c d

def ifLt (a b c d : RatExpr v) : RatExpr v := ifLe b a d c
def ifEq (a b c d : RatExpr v) : RatExpr v := ifLe a b (ifLe b a c d) d
def max (a b : RatExpr v) : RatExpr v := ifLe a b b a
def min (a b : RatExpr v) : RatExpr v := ifLe a b a b
end RatExpr
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ProgressionExpressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace NatExpr
variable {v : Type*}
def min (a b : NatExpr v) : NatExpr v := .iteLe a b a b
def max (a b : NatExpr v) : NatExpr v := .iteLe a b b a
@[simp] lemma eval_min (x : v → ℕ) (a b : NatExpr v) : (min a b).eval x=Min.min (a.eval x) (b.eval x) := by
  simp [min,eval,min_def]
@[simp] lemma eval_max (x : v → ℕ) (a b : NatExpr v) : (max a b).eval x=Max.max (a.eval x) (b.eval x) := by
  simp [max,eval,max_def]
end NatExpr

namespace OrderTrial.Expressions
variable {v : Type*}
open RatExpr

def powerSum (q : ℕ) (M : RatExpr v) : RatExpr v := match q with
  | 0 => M
  | 1 => M*(M-1)/2
  | 2 => M*(M-1)*(2*M-1)/6
  | 3 => (M*(M-1)/2)^2
  | 4 => M*(M-1)*(2*M-1)*(3*M^2-3*M-1)/30
  | _ => 0

def fiveTerm (a : ℕ → RatExpr v) (lo hi : NatExpr v) : RatExpr v :=
  ifNatLe lo hi (RatExpr.sum (fun q => a q*(powerSum q (ofNat hi)-powerSum q (ofNat lo))) 5) 0

def linear (a b : RatExpr v) (lo hi : NatExpr v) : RatExpr v :=
  fiveTerm (fun q => if q=0 then a else if q=1 then b else 0) lo hi

def ramp (a b : RatExpr v) (M : NatExpr v) : RatExpr v :=
  ifLt 0 b (linear a b ((-a/b).ceilNat) M)
    (ifLt b 0 (linear a b (.const 0) (NatExpr.min M (-a/b).ceilNat))
      (ofNat M*RatExpr.max 0 a))

def phaseRe (a b : RatExpr v) (M : NatExpr v) : RatExpr v :=
  -ofNat M+4*linear (a+1/2) b (.const 0) M-8*ramp a b M+
    8*ramp (a-1/2) b M-8*ramp (a-1) b M

def phaseIm (a b : RatExpr v) (M : NatExpr v) : RatExpr v :=
  4*linear (a+1/2) b (.const 0) M-8*ramp (a+1/4) b M+
    8*ramp (a-1/4) b M-8*ramp (a-3/4) b M+8*ramp (a-5/4) b M

def binE (Q d j : NatExpr v) : NatExpr v :=
  .div (.add (.mul (.mul (.const 2) j) Q) d) (.mul (.const 2) d)

def error (Q d j : NatExpr v) : RatExpr v := ofNat (binE Q d j)-ofNat j*ofNat Q/ofNat d

def offset (Q d j t : NatExpr v) : RatExpr v :=
  ofNat (.mod (.mul j t) d)/ofNat d+error Q d j*ofNat t/ofNat Q

def slope (Q d j : NatExpr v) : RatExpr v := error Q d j*ofNat d/ofNat Q

def count (Q d t : NatExpr v) : NatExpr v := .add (.div (.sub (.sub Q (.const 1)) t) d) (.const 1)

/-- A literal finite arithmetic template for P. Its size is independent of Q,
B,d,j,t; there is no enumeration of the phase-register range. -/
def probability (Q d j t : NatExpr v) : RatExpr v :=
  (phaseRe (offset Q d j t) (slope Q d j) (count Q d t)^2+
   phaseIm (offset Q d j t) (slope Q d j) (count Q d t)^2)/(ofNat Q)^2
end OrderTrial.Expressions
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PolynomialFilterExpressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
namespace NatExpr
variable {v : Type*}
def pow (a : NatExpr v) : ℕ → NatExpr v
  | 0 => .const 1
  | n+1 => .mul (pow a n) a
@[simp] lemma eval_pow (x : v → ℕ) (a : NatExpr v) (n : ℕ) :
    (pow a n).eval x=(a.eval x)^n := by
  induction n with
  | zero => simp [pow,eval]
  | succ n ih => simp [pow,eval,ih,pow_succ]
end NatExpr

namespace RatExpr
variable {v : Type*}
def sumList {α : Type*} (f : α → RatExpr v) : List α → RatExpr v
  | [] => 0
  | a::as => f a+sumList f as
end RatExpr

namespace OrderTrial.Expressions
variable {v : Type*}
open RatExpr

def rampPoly (q a : ℤ) : PolyExpr v :=
  if a ≤ q then (.X-.const ((a:ℚ)/4))^2 else 0
def rampLin (q a : ℤ) : PolyExpr v :=
  if a ≤ q then .X-.const ((a:ℚ)/4) else 0

def splineRePoly (q : ℤ) : PolyExpr v :=
  -(.X+.const (1/2))+2*(.X+.const (1/2))^2-4*rampPoly q 0+
    4*rampPoly q 2-4*rampPoly q 4
def splineImPoly (q : ℤ) : PolyExpr v :=
  2*(.X+.const (1/2))^2-4*rampPoly q (-1)+4*rampPoly q 1-
    4*rampPoly q 3+4*rampPoly q 5-.const (1/4)
def phaseRePoly (q : ℤ) : PolyExpr v :=
  -1+4*(.X+.const (1/2))-8*rampLin q 0+8*rampLin q 2-8*rampLin q 4
def phaseImPoly (q : ℤ) : PolyExpr v :=
  4*(.X+.const (1/2))-8*rampLin q (-1)+8*rampLin q 1-
    8*rampLin q 3+8*rampLin q 5

def linearPoly (d : NatExpr v) (η : RatExpr v) : PolyExpr v := .C ((ofNat d)⁻¹)*.X+.C η

def integralZero (d : NatExpr v) (A : PolyExpr v) : PolyExpr v :=
  .C ((ofNat d)⁻¹)*A.comp (linearPoly d 0)
def integralSlope (d : NatExpr v) (η : RatExpr v) (G₀ G₁ : PolyExpr v) : PolyExpr v :=
  .C ((ofNat d*η)⁻¹)*(G₁.comp (linearPoly d η)-G₀.comp (linearPoly d 0))
def massZero (d : NatExpr v) (q₀ : ℤ) : PolyExpr v :=
  integralZero d (phaseRePoly q₀)^2+integralZero d (phaseImPoly q₀)^2
def massSlope (d : NatExpr v) (η : RatExpr v) (q₀ q₁ : ℤ) : PolyExpr v :=
  integralSlope d η (splineRePoly q₀) (splineRePoly q₁)^2+
  integralSlope d η (splineImPoly q₀) (splineImPoly q₁)^2

def massCoeff (d : NatExpr v) (η : RatExpr v) (q₀ q₁ : ℤ) (k : ℕ) : RatExpr v :=
  ifEq η 0 ((massZero d q₀).coeff k) ((massSlope d η q₀ q₁).coeff k)

def rounded (D : NatExpr v) (a : RatExpr v) : RatExpr v :=
  ofInt (ofNat D*a).ceil/ofNat D

def roundingDen (Q B : NatExpr v) : NatExpr v := .mul Q (NatExpr.pow B 8)

def low (d : NatExpr v) (η : RatExpr v) (q : ℤ×ℤ) : NatExpr v :=
  NatExpr.max (ofNat d*const q.1/4).ceilNat (ofNat d*(const q.2/4-η)).ceilNat
def high (d : NatExpr v) (η : RatExpr v) (q : ℤ×ℤ) : NatExpr v :=
  NatExpr.min d (NatExpr.min (ofNat d*(const q.1+1)/4).ceilNat
    (ofNat d*((const q.2+1)/4-η)).ceilNat)

def pieceSum (Q B d j : NatExpr v) (q : ℤ×ℤ) : RatExpr v :=
  let η := error Q d j
  let lo := low d η q
  let hi := high d η q
  fiveTerm (fun k => rounded (roundingDen Q B) (massCoeff d η q.1 q.2 k)) lo hi+
    ofNat (.sub hi lo)*(64/ofNat Q)

/-- Literal fixed 32-piece table; no noncomputable Finset enumeration is used
by the circuit generator. -/
def quarterList : List (ℤ×ℤ) :=
  ([0,1,2,3] : List ℤ).flatMap (fun q => ([-2,-1,0,1,2,3,4,5] : List ℤ).map (q,·))

def majorantSumE (Q B d j : NatExpr v) : RatExpr v :=
  sumList (pieceSum Q B d j) quarterList/2

end OrderTrial.Expressions
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_DynamicMajorantExpressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial.Expressions
variable {v : Type*}
open RatExpr

def dynamicRamp (q : IntExpr v) (a : ℤ) : PolyExpr v :=
  .C (ifIntLe (.ofInt a) q 1 0)*(.X-.const ((a:ℚ)/4))^2
def dynamicRampLin (q : IntExpr v) (a : ℤ) : PolyExpr v :=
  .C (ifIntLe (.ofInt a) q 1 0)*(.X-.const ((a:ℚ)/4))

def dynamicSplineRe (q : IntExpr v) : PolyExpr v :=
  -(.X+.const (1/2))+2*(.X+.const (1/2))^2-4*dynamicRamp q 0+
    4*dynamicRamp q 2-4*dynamicRamp q 4
def dynamicSplineIm (q : IntExpr v) : PolyExpr v :=
  2*(.X+.const (1/2))^2-4*dynamicRamp q (-1)+4*dynamicRamp q 1-
    4*dynamicRamp q 3+4*dynamicRamp q 5-.const (1/4)
def dynamicPhaseRe (q : IntExpr v) : PolyExpr v :=
  -1+4*(.X+.const (1/2))-8*dynamicRampLin q 0+8*dynamicRampLin q 2-8*dynamicRampLin q 4
def dynamicPhaseIm (q : IntExpr v) : PolyExpr v :=
  4*(.X+.const (1/2))-8*dynamicRampLin q (-1)+8*dynamicRampLin q 1-
    8*dynamicRampLin q 3+8*dynamicRampLin q 5


def dynamicMassZero (d : NatExpr v) (q₀ : IntExpr v) : PolyExpr v :=
  integralZero d (dynamicPhaseRe q₀)^2+integralZero d (dynamicPhaseIm q₀)^2
def dynamicMassSlope (d : NatExpr v) (η : RatExpr v) (q₀ q₁ : IntExpr v) : PolyExpr v :=
  integralSlope d η (dynamicSplineRe q₀) (dynamicSplineRe q₁)^2+
    integralSlope d η (dynamicSplineIm q₀) (dynamicSplineIm q₁)^2

def dynamicMassCoeff (d : NatExpr v) (η : RatExpr v) (q₀ q₁ : IntExpr v) (k : ℕ) : RatExpr v :=
  ifEq η 0 ((dynamicMassZero d q₀).coeff k) ((dynamicMassSlope d η q₀ q₁).coeff k)

def quarter (a : RatExpr v) : IntExpr v := (4*a).floor

/-- Actual constant-depth arithmetic for U, including dynamic quarter selection.
No residue loop and no polynomial-valued oracle occurs in this expression. -/
def majorantE (Q B d j u : NatExpr v) : RatExpr v :=
  let η := error Q d j
  let q₀ := quarter (ofNat u/ofNat d)
  let q₁ := quarter (ofNat u/ofNat d+η)
  RatExpr.sum (fun k => rounded (roundingDen Q B) (dynamicMassCoeff d η q₀ q₁ k)*(ofNat u)^k) 5+
    64/ofNat Q

end ExactQuantumFactoring.OrderTrial.Expressions


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetentionExpressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial.Expressions
open RatExpr
variable {v : Type*}

/-- Bounded priority search for the least covering power of two.  The bounds
are compile-time constants, not exponentiation gates with variable exponents. -/
def coveringPow (d : NatExpr v) : ℕ → NatExpr v
  | 0 => .const 1
  | k+1 => .iteLe d (.const (2^k)) (coveringPow d k) (.const (2^(k+1)))

def lambdaE (n : ℕ) (d : NatExpr v) : RatExpr v :=
  1/ofNat (.mul (.const 1024) (coveringPow d n))

def coefficientE (n : ℕ) (Q B d j : NatExpr v) : RatExpr v :=
  ofInt ((ofNat (.const (2^(10*n))) * lambdaE n d / majorantSumE Q B d j).floor) /
    ofNat (.const (2^(10*n)))

def remainderE (n : ℕ) (Q B d j : NatExpr v) : RatExpr v :=
  lambdaE n d - coefficientE n Q B d j * majorantSumE Q B d j

def discrepancyE (n : ℕ) (Q B d j t : NatExpr v) : RatExpr v :=
  2*(ofNat B)^3*(majorantE Q B d j (.mod (.mul j t) d)-probability Q d j t)*coefficientE n Q B d j

def thirdRetentionE (n : ℕ) (Q B d j : NatExpr v) : RatExpr v :=
  4*(ofNat B)^2*remainderE n Q B d j

end ExactQuantumFactoring.OrderTrial.Expressions


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExpressionSharing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NatExpr
variable {v : Type*}

/-- Only truncated subtraction duplicates its operands in the actual compiler.
In particular a priority-search tail in an ite is compiled ONCE, not twice. -/
def sharedCost : NatExpr v → ℕ
  | .var _ | .const _ => 1
  | .add a b | .mul a b | .div a b | .mod a b => a.sharedCost+b.sharedCost+1
  | .sub a b => 2*(a.sharedCost+b.sharedCost)+1
  | .iteLe a b c d => a.sharedCost+b.sharedCost+c.sharedCost+d.sharedCost+1

end NatExpr
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetentionCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic

namespace OrderTrial.Expressions
variable {v : Type*}

def firstE (n : ℕ) (d j : NatExpr v) : RatExpr v :=
  coefficientE n (.const ((2^n)^16)) (.const (2^n)) d j
def secondE (n : ℕ) (d j t : NatExpr v) : RatExpr v :=
  discrepancyE n (.const ((2^n)^16)) (.const (2^n)) d j t
def lastE (n : ℕ) (d j : NatExpr v) : RatExpr v :=
  thirdRetentionE n (.const ((2^n)^16)) (.const (2^n)) d j

end OrderTrial.Expressions
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TrialControlCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork BitArithmetic

inductive DecodeVar | den | num | residue | coin

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SortedWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
namespace SortedWords

def LEWord {w : ℕ} (a b : Basis w) : Prop := PaddedOrder (bitsValue a).toNat (bitsValue b).toNat
instance instDecidableLEWord {w : ℕ} (a b : Basis w) : Decidable (LEWord a b) :=
  inferInstanceAs (Decidable (_=0 ∨ (_≠0 ∧ _ ≤ _)))

def insert {w : ℕ} (a : Basis w) : List (Basis w)→List (Basis w)
  | []=>[a]
  | b::bs=>if LEWord a b then a::insert b bs else b::insert a bs

def sort {w : ℕ} : List (Basis w)→List (Basis w)
  | []=>[]
  | a::as=>insert a (sort as)

end SortedWords
end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SortedEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic.SortedWords

def numbers {w : ℕ} (xs : List (Basis w)) : List ℕ := xs.map (fun a=>(bitsValue a).toNat)

end ExactQuantumFactoring.BitArithmetic.SortedWords


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ChildQueueCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic.ChildQueue
open SortedWords

def naturalKids (xs : List ℕ) : List ℕ :=
  (xs.dedup.filter (fun a=>2<a)).map (·-1)

end ExactQuantumFactoring.BitArithmetic.ChildQueue


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalTreeQueue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace PhysicalTree
abbrev capacity (n : ℕ) := 2*n^2+1
abbrev configWidth (n : ℕ) := capacity n*n

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalDataLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace PhysicalTree

/-- Concrete flat complete-data condition sufficient for retrospective lookup:
root present, every required child present, and every non-dummy row a complete
prime factorization. Equal labels from different parents are NOT collapsed. -/
def CompleteLog (n N : ℕ) (rows : List (ℕ×List ℕ)) : Prop :=
  N∈rows.map Prod.fst ∧
  (∀ a∈rows, a.1=0 ∨ CorrectEncoding a.1 n a.2) ∧
  (∀ a∈rows, ∀ d∈AuxiliaryTree.children a.1, d∈rows.map Prod.fst)

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FlatVerifiedData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree
namespace PhysicalTree

/-- Data lookup runs on the retained flat rows, not on a factorization oracle. -/
def lookupFields (rows : List (ℕ×List ℕ)) (m : ℕ) : List ℕ :=
  match rows.find? (fun r=>decide (r.1=m)) with
  | none=>[]
  | some r=>r.2

def lookupPrimes (rows : List (ℕ×List ℕ)) (m : ℕ) : List ℕ :=
  (lookupFields rows m).filter (fun p=>decide (p≠0))

def logDivisorPrimes (rows : List (ℕ×List ℕ)) (M m : ℕ) : List ℕ :=
  divisorPrimes m (lookupPrimes rows M)

/-- The only factor data used are supplied parent factors and already verified
p−1 rows. This representation is a mathematical list interface; its Boolean
implementation is a separate obligation, not hidden in this definition. -/
noncomputable def logTotientPrimes (rows : List (ℕ×List ℕ)) (M m : ℕ) : List ℕ :=
  let f:=primeRecord (logDivisorPrimes rows M m)
  (f.support.sort (·≤·)).flatMap (fun p=>
    List.replicate (f p-1) p ++ if p=2 then [] else lookupPrimes rows (p-1))

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TableOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree

namespace PhysicalTree
/-- A fixed rectangular table of prime candidates. Unused rows and zero
padding become 2. This requires no support enumeration or factor search. -/
def tableFactors (rows : List (ℕ×List ℕ)) : List ℕ :=
  rows.flatMap (fun r=>r.2.map (fun p=>if r.1=0 ∨ p=0 then 2 else p))

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TablePrimeSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree

/-- A distinguished component can be tested by polynomially many pairwise
comparisons, without constructing the least prime factor of an unknown N. -/
def leastDivisorIn (ps : List ℕ) (m p : ℕ) : Prop := ∀ q∈ps,q∣m→p≤q

/-- Redundant rectangular-table entries and harmless dummy primes are ignored
unless they divide m; duplicates impose exactly the same congruence. -/
noncomputable def tableCanonical (ps : List ℕ) (a m n : ℕ) : Prop := by
  classical
  exact a < m ∧ ∀ p∈ps,p∣m→a%(Nat.gcd m (p^n))=
    if leastDivisorIn ps m p then 1 else Nat.gcd m (p^n)-1

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CanonicalResidueCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace BitArithmetic
attribute [local instance] Classical.propDecidable

def componentCongruenceBound (n l c : ℕ) : ℕ :=
  c+3*primeComponentBound n c+216*n*n+500*n+100+
    l*(4*c+216*n*n+202*n+42)

def tableCanonicalBound (n l c : ℕ) : ℕ :=
  2*c+48*n+10+l*(2*c+216*n*n+154*n+33+componentCongruenceBound n l c)+2

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ChildQueueBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic.ChildQueue
open BooleanNetwork

def oneBound (s w c r : ℕ) := c+49*w+11+r*(2*c+96*w+25)+s*w*(c+159*w+6)+7*(s*w)

end ExactQuantumFactoring.BitArithmetic.ChildQueue


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CircuitEmissionModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission
def gateView (g : Gate):= (g.primitive,g.inverse,g.controlled)
end ExactQuantumFactoring.CircuitEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ClosedLevelCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace BitArithmetic

def oddPartBound (n c : ℕ) : ℕ := c+primeComponentBound n (c+n)+216*n*n+56*n+6

def closedLevelBound (n c : ℕ) : ℕ := oddPartBound n c+c+1000*n*n+1000*n+100
end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CompletionFilterCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace Completion
namespace Expressions
variable {v : Type*}

def ordinaryMass (t : ℕ) (s : RatExpr v) : RatExpr v :=
  (RatExpr.const (1-1/(2:ℚ)^t)).mul s

def coefficient (W t : ℕ) (s z : RatExpr v) : RatExpr v :=
  (RatExpr.ofInt (((RatExpr.const ((2:ℚ)^(W+t+2))).mul
    (z.div (ordinaryMass t s))).floor)).div (RatExpr.const ((2:ℚ)^(W+t+2)))

def guess (W t : ℕ) (s z : RatExpr v) : RatExpr v :=
  ((z.sub ((coefficient W t s z).mul (ordinaryMass t s))).mul
    (RatExpr.const ((2:ℚ)^W))).div (RatExpr.const (1/(2:ℚ)^t))

end Expressions

end Completion
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ComponentPhiCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace BitArithmetic

def componentPhiBound (n c : ℕ) : ℕ := 4*primeComponentBound n c+2*c+1000*n*n+1000*n+100

def componentLevelBound (n c : ℕ) : ℕ :=
  2*c+216*n*n+308*n+50+closedLevelBound n (componentPhiBound n c)+8*n
end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PolyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring

/-- A worst-case bound for all input lengths, with nonnegative coefficients. -/
def PolyBound (f : ℕ → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, f n ≤ p.eval n




end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RationalPowerCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
namespace IntExpr
variable {v : Type*}

/-- Power of a balanced signed integer without the exponentially expanding
positive/negative multiplication tree. The sign test is static in parity and
uses only absolute value and linear-length natural-power expressions. -/
def signedPower (a : IntExpr v) (k : ℕ) : IntExpr v :=
  let M:=ofNat (a.natAbs.pow k)
  if Even k then M else iteLe a.neg a.pos M M.negation

@[simp] lemma eval_signedPower (x : v→ℕ) (a : IntExpr v) (k : ℕ) :
    (signedPower a k).eval x=(a.eval x)^k := by
  have hm : (ofNat (a.natAbs.pow k)).eval x=|a.eval x|^k := by
    simp only [eval_ofNat,NatExpr.eval_pow,eval_natAbs,Nat.cast_pow,Int.natCast_natAbs]
  unfold signedPower
  split_ifs with hk
  · rw [hm]
    exact hk.pow_abs _
  · rw [eval_iteLe,eval_negation,hm]
    have ho : Odd k := Nat.not_even_iff_odd.mp hk
    by_cases hp : a.neg.eval x≤a.pos.eval x
    · rw [ite_eq_left hp,abs_of_nonneg]
      dsimp only [eval]
      omega
    · rw [ite_eq_right hp,abs_of_neg,ho.neg_pow,neg_neg]
      dsimp only [eval]
      omega

end IntExpr
namespace RatExpr
variable {v : Type*}

/-- Exact rational power, with polynomial syntax in k, including zero
unreduced denominators. Existing `pow` and its semantics are not changed. -/
def signedPower (a : RatExpr v) (k : ℕ) : RatExpr v :=
  ⟨a.num.signedPower k,a.den.pow k⟩

@[simp] lemma eval_signedPower (x : v→ℕ) (a : RatExpr v) (k : ℕ) :
    (a.signedPower k).eval x=(a.eval x)^k := by
  simp only [signedPower,eval,IntExpr.eval_signedPower,NatExpr.eval_pow,
    Int.cast_pow,Nat.cast_pow,div_pow]

/-- The repeated-success expression used by both real transitions, without
an exponentially expanded balanced-integer numerator syntax. -/
def repeatedSuccess (a : RatExpr v) (K : ℕ) : RatExpr v :=
  (const 1).sub (((const 1).sub a).signedPower K)

end RatExpr
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExpressionResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring

namespace NatExpr
variable {v : Type*}

/-- Actual syntax length, sharing-sensitive compiler cost and constant bit size. -/
def weight (e : NatExpr v) : ℕ := e.size + e.sharedCost + e.maxConst.size
@[simp] lemma weight_var (a : v) : (var a).weight = 2 := rfl
@[simp] lemma weight_const (a : ℕ) : (const (v:=v) a).weight = a.size+2 := by
  simp [weight,size,sharedCost,maxConst]; omega
end NatExpr

/-- Uniform polynomial growth of a family of literal natural expressions.
Nothing here bounds the values of dynamic variables or assumes arithmetic is free. -/
def NatExprPoly {v : ℕ → Type*} (f : ∀ n, NatExpr (v n)) : Prop :=
  PolyBound (fun n => (f n).weight)

end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RationalExpressionResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring

/-- All balanced integer components have polynomial literal circuit syntax. -/
def IntExprPoly {v : ℕ → Type*} (a : ∀ n, IntExpr (v n)) : Prop :=
  NatExprPoly (fun n => (a n).pos) ∧ NatExprPoly (fun n => (a n).neg)

/-- Polynomial literal numerator and denominator syntax; no bound on dynamic values is assumed. -/
def RatExprPoly {v : ℕ → Type*} (a : ∀ n, RatExpr (v n)) : Prop :=
  IntExprPoly (fun n => (a n).num) ∧ NatExprPoly (fun n => (a n).den)
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PolynomialExpressionResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring

/-- Every fixed-index coefficient of this family has polynomial syntax. -/
def PolyExprPoly {v : ℕ → Type*} (a : ∀ n, PolyExpr (v n)) : Prop :=
  ∀ k, RatExprPoly (fun n => (a n).coeff k)

end ExactQuantumFactoring

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ConcreteExpressionResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring

/-- Substitution-stable, fixed-depth polynomial schemas. In particular this
controls the literal syntax of every fixed coefficient, not just its denotation. -/
def PolySchemaPoly {v : ℕ → Type*} (a : ∀ n, PolyExpr (v n)) : Prop :=
  ∀ b : ∀ n, PolyExpr (v n), PolyExprPoly b → PolyExprPoly (fun n => (a n).comp (b n))

end ExactQuantumFactoring
end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SignedSyntaxEmission
attribute [-instance] _root_.OAI.ExactQuantumFactoring.RatExpr.instAdd _root_.OAI.ExactQuantumFactoring.RatExpr.instDiv _root_.OAI.ExactQuantumFactoring.RatExpr.instInv _root_.OAI.ExactQuantumFactoring.RatExpr.instMul _root_.OAI.ExactQuantumFactoring.RatExpr.instNeg _root_.OAI.ExactQuantumFactoring.RatExpr.instOfNat _root_.OAI.ExactQuantumFactoring.RatExpr.instPowNat _root_.OAI.ExactQuantumFactoring.RatExpr.instSub
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram
variable {v : Type}
def intExprView (a : IntExpr v):=(a.pos,a.neg)
def ratExprView (a : RatExpr v):=(a.num,a.den)
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExpressionPowerEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram
variable {v : Type} (ev : v→List Bool)

def exprPowerStep (s : NatExpr v×NatExpr v) : NatExpr v×NatExpr v:=(s.1,.mul s.2 s.1)
lemma exprPowerStep_fst (s : NatExpr v×NatExpr v) (i : ℕ) : ((exprPowerStep^[i]) s).1=s.1:=by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply'];exact ih
lemma exprPowerStep_start (a : NatExpr v) (i : ℕ) :
    (exprPowerStep^[i]) (a,.const 1)=(a,a.pow i):=by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply',ih];rfl
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CoveringPowerEmission
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NatExpr.weight_const _root_.OAI.ExactQuantumFactoring.NatExpr.weight_var
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram
variable {v : Type} (ev : v→List Bool)
lemma bits_length_max_le (a b : ℕ) : (max a b).bits.length≤a.bits.length+b.bits.length:=by
  rcases le_total a b with h|h
  · rw [max_eq_right h];omega
  · rw [max_eq_left h];omega

def coveringStep (s : ℕ×(NatExpr v×NatExpr v)) : ℕ×(NatExpr v×NatExpr v):=
  (s.1*2,s.2.1,.iteLe s.2.1 (.const s.1) s.2.2 (.const (s.1*2)))
lemma coveringStep_pow (s : ℕ×(NatExpr v×NatExpr v)) (i : ℕ) :
    ((coveringStep^[i]) s).1=s.1*2^i:=by
  induction i with
  | zero=>simp
  | succ i ih=>rw [Function.iterate_succ_apply'];change ((coveringStep^[i]) s).1*2=_
               rw [ih,pow_succ,Nat.mul_assoc]
lemma coveringStep_base (s : ℕ×(NatExpr v×NatExpr v)) (i : ℕ) :
    ((coveringStep^[i]) s).2.1=s.2.1:=by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply'];exact ih
lemma coveringStep_pow_size (s : ℕ×(NatExpr v×NatExpr v)) (i : ℕ) :
    (((coveringStep^[i]) s).1).bits.length≤(s.1).bits.length+2*i+1:=by
  rw [coveringStep_pow]
  have hm:=bits_length_mul s.1 (2^i)
  have hp:=bits_length_pow 2 i
  have ht : (2:ℕ).bits.length=2:=rfl
  rw [ht] at hp;omega
lemma coveringStep_start (d : NatExpr v) (i : ℕ) :
    (coveringStep^[i]) (1,d,.const 1)=(2^i,d,OrderTrial.Expressions.coveringPow d i):=by
  induction i with
  | zero=>rfl
  | succ i ih=>rw [Function.iterate_succ_apply',ih];simp only [coveringStep,pow_succ,OrderTrial.Expressions.coveringPow]
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PolyAt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
/-- Uniform polynomial bounds over arbitrary auxiliary parameters. Only the
chosen length is charged, so this also records worst-case bounds over all
finite loop indices and all networks satisfying a supplied count invariant. -/
def PolyAt {α : Sort*} (length : α→ℕ) (f : α→ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ a,f a≤p.eval (length a)

end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExpressionTokenProcedure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram
namespace Emission

def tokenTag : ExprToken ℕ→ℕ | .inl _=>0 | .inr (.inl _)=>1 | .inr (.inr _)=>2
def tokenPayload : ExprToken ℕ→ℕ | .inl i=>i | .inr (.inl c)=>c | .inr (.inr j)=>j
end Emission
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExpressionTemplateEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram
variable {v : Type}
def tokenMap (f : v→ℕ) : ExprToken v→ExprToken ℕ:=Sum.map f id
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalTreeLaunch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace PhysicalTree

abbrev steps (n : ℕ) := 2*n^2

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_VerifiedTreeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace PhysicalNode
abbrev resultBound (n : ℕ) := n*n+n*n*(498*n+114)
end PhysicalNode
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_VerifiedTableOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace BitArithmetic

/-- The extra n bits make zero-extension unconditional, including empty
malformed tables. On verified input this holds the entire repeated product. -/
def tableOrderWidth (n f : ℕ) : ℕ := n*(n*f)+n+1

/-- This bound is polynomial in n, table length and the individual stored-word
circuit cost. Resizing is itself a bounded circuit, not a word-RAM primitive. -/
def tableOrderBound (n f c : ℕ) : ℕ :=
  let w:=tableOrderWidth n f
  let C:=3*c+220*n+50+w
  (n*f)*(C+90*w*w+14*w+6+stripStepBound w C)+w+n

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TableFavorable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

/-- Pairwise comparison avoids searching for a least component. The supplied
rectangular table may contain duplicates and harmless primes not dividing m. -/
noncomputable def tableFavorable (ps : List ℕ) (data : FactorData) (a m n : ℕ) : Prop :=
  a < m  ∧  a.Coprime m  ∧   ¬ ∀ p∈ps,p ∣ m→∀ q∈ps,q ∣ m→
    padicValNat 2 (dataOrder data a (Nat.gcd m (p^n)))=
      padicValNat 2 (dataOrder data a (Nat.gcd m (q^n)))

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TableTotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

/-- Strip a given prime multiset, updating Euler's totient one prime factor
at a time. The supplied list may contain redundant factors. -/
def totientScan : List ℕ → ℕ → ℕ
  | [], _ => 1
  | p::ps, v => if p ∣ v then
      (if p ∣ v/p then p else p-1)*totientScan ps (v/p)
    else totientScan ps v

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TotientAccumulator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

/-- The finite-word accumulator semantics. Only the multiplicative
accumulator is reduced; division of the residual never overflows. -/
def totientStepNat (B p : ℕ) (s : ℕ×ℕ) : ℕ×ℕ :=
  if p ∣ s.1 then (s.1/p,(s.2*(if p ∣ s.1/p then p else p-1))%B) else s

def totientFoldNat (B : ℕ) : List ℕ → (ℕ×ℕ) → (ℕ×ℕ)
  | [], s => s
  | p::ps, s => totientFoldNat B ps (totientStepNat B p s)

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TotientCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace BitArithmetic

/-- A loose but explicit uniform polynomial bound; the residual, prime and
accumulator subcircuits are evaluated a constant number of times per step. -/
def totientStepBound (w c : ℕ) : ℕ := 30*c+3000*w*w+3000*w+300

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TableTotientCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace BitArithmetic

def tableTotientBound (n f c : ℕ) : ℕ := c+n+(n*f)*totientStepBound n (3*c+220*n+50)

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TableFavorableCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
open scoped BigOperators
namespace BitArithmetic

def tableBadCountBound (n f c : ℕ) : ℕ :=
  (n+1)*(f*(componentLevelBound n c+90*n*n+22*n+7+f*(2*c+96*n+25))+n+86*n+6)+n

def tableFavorableCountBound (n f c : ℕ) : ℕ :=
  2*(c+n+(n*f)*totientStepBound n c)+2*tableBadCountBound n f c+214*n+15

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedListFilter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace Completion.Expressions

def listRateCoin (n K : ℕ) : RatExpr (Fin 3) :=
  ((RatExpr.ofNat (v:=Fin 3) (.var 1)).div
    (RatExpr.ofNat (OrderTrial.Expressions.coveringPow (.var 0) n))).repeatedSuccess K

end Completion.Expressions

namespace NodeMachine
variable {n c : ℕ}

abbrev listCoinWidth (n : ℕ) := Completion.coinBits (Completion.transitionWidth n) (2*n) (n*n^5)
abbrev listVarWidth (n : ℕ) := n+listCoinWidth n

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedOrderFilter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace Completion.Expressions

def orderRateCoin (n K : ℕ) : RatExpr (Fin 3) :=
  ((RatExpr.ofNat (v:=Fin 3) (.var 1)).mul (OrderTrial.Expressions.lambdaE n (.var 0))).repeatedSuccess K
end Completion.Expressions
namespace NodeMachine
variable {n c : ℕ}
abbrev orderVarWidth (n : ℕ) := n+OrderSlots.coinWidth n

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetrospectiveSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree OrderTrial

/-- The usable-slot test is just range plus Euclidean gcd, not an order oracle. -/
def residueUsable (a m : ℕ) : Prop := a < m ∧ a.Coprime m

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FlatDataView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree

/-- Precisely the supplied local record and p−1 lookup facts consumed by the
retrospective arithmetic. This is established below from actual verified rows. -/
def DataView (d : FactorData) (M : ℕ) : Prop :=
  d.factors=M.factorization ∧
    ∀ l∈children M,dataChildPrimes d l=recordPrimes l.factorization

namespace PhysicalTree
noncomputable def rowData (r : ℕ×List ℕ) : FactorData :=
  .node r.1 (primeRecord (r.2.filter (fun p=>decide (p≠0)))) []
noncomputable def flatData (rows : List (ℕ×List ℕ)) (M : ℕ) : FactorData :=
  .node M (primeRecord (lookupPrimes rows M)) (rows.map rowData)
@[simp] lemma rowData_label (r : ℕ×List ℕ) : (rowData r).label=r.1 := rfl
end PhysicalTree

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_QuarterPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness OrderTrial

namespace Quarter
/-- The second rounding uses EXACTLY J+2, not the transition completion's
slightly finer W+t+2 grid. One surplus fair retention bit is harmless. -/
def retention (n : ℕ) : ℚ := quarterCoeff (n*n) (knownProbability n)
def guessRetention (n : ℕ) : ℚ := (2:ℚ)^(n*n+1)*quarterRemainder (n*n) (knownProbability n)
abbrev D (n : ℕ) : ℕ := Completion.coinBits (n*n) 1 (n^11)

/-- No probability or canonical factor list occurs in the raw unitary. -/
def program {q : ℕ} (P : List (Instruction q)) (n : ℕ) := Completion.program P (n*n) 1 (n^11)

end Quarter
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreePadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials
namespace PhysicalTree

/-- The actual tree has 2n² nodes, 2n split clocks per node, one list slot and
n^5 padded base/order slots per split. This is not the n^10 padding cap. -/
def slots (n : ℕ) : ℕ := ((n^5+1)*(2*n))*(2*n^2)
def padding (n : ℕ) : ℕ := n^10-slots n

def padProgram (n : ℕ) : List (Instruction (tensorWidth n (padding n))) :=
  tensorProgram (hadamardPrefix n n le_rfl) (padding n)

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExactnessFurther2
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
namespace ExactQuantumFactoring
open scoped BigOperators

open Exactness

/-- A syntactic read-only rule suffices; no hypothesis about the state prepared
by the algorithm or its unknown factors occurs here. -/
def ReadOnly {q : ℕ} (inputs : Finset (Fin q)) (P : List (Instruction q)) : Prop :=
  ∀ o∈P,o.target∉inputs

def inputSector {q : ℕ} (inputs : Finset (Fin q)) (z x : Basis q) : Prop :=
  ∀ i∈inputs,x i=z i

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OracleReadOnly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork

@[simp] lemma Instruction.target_reverse {q : ℕ} (o : Instruction q) : o.reverse.target=o.target := rfl
@[simp] lemma Instruction.target_place {p q : ℕ} (w : Register p q) (o : Instruction p) :
    (o.place w).target=w o.target := rfl
@[simp] lemma notAt_target {q : ℕ} (t : Fin q) : (notAt t).target=t := rfl
@[simp] lemma cnotAt_target {q : ℕ} (a t : Fin q) (ha : a≠t) : (cnotAt a t ha).target=t := rfl

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactoringRelabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
/-- Move the physical input after the branch bit to the front, and place the
readout immediately after the true input. The retained history is permuted,
never erased or initialized with input-dependent advice. -/
def relocateVal (A m ℓ i : ℕ) : ℕ :=
  if i=0 then ℓ+m else if i≤ℓ then i-1 else if i<A then i+m
  else if i<A+m then ℓ+(i-A) else i

lemma relocateVal_lt {A m ℓ r i : ℕ} (hl : ℓ+1≤A) (hi : i<A+m+r) :
    relocateVal A m ℓ i<A+m+r := by
  unfold relocateVal
  split_ifs <;> omega

lemma relocateVal_injective {A m ℓ r : ℕ} (hl : ℓ+1≤A) :
    Function.Injective (fun i : Fin (A+m+r) => relocateVal A m ℓ i.val) := by
  intro i j h
  apply Fin.ext
  have hi:=i.isLt
  have hj:=j.isLt
  dsimp only at h
  unfold relocateVal at h
  split_ifs at h <;> omega

def relocate (A m ℓ r : ℕ) (hl : ℓ+1≤A) : Register (A+m+r) (A+m+r) where
  toFun i:=⟨relocateVal A m ℓ i.val,relocateVal_lt hl i.isLt⟩
  inj' := by
    intro i j h
    exact relocateVal_injective hl (congrArg Fin.val h)

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactoringCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork BitArithmetic Exactness
namespace PhysicalTree

lemma paddedLength_pos (ℓ : ℕ) : 0<paddedLength ℓ := by
  unfold paddedLength;omega

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_EmissionBoundedRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool}

def recursionNext (K : α→ℕ) (x : Σa,Fin (K a+1)) : Σa,Fin (K a+1):=
  ⟨x.1,⟨min (x.2.val+1) (K x.1),by omega⟩⟩
end ExactQuantumFactoring.BitStackProgram.Emits

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ExpressionAt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork

def NatExprAt {α : Type*} (len : α→ℕ) {v : α→Type*} (e : ∀x,NatExpr (v x)) :=
  PolyAt len (fun x=>(e x).weight)
end ExactQuantumFactoring

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkFoldChoiceEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram
lemma quadBudget_bound (a b c d A B N : ℕ) (ha : a≤A) (hb : b≤B)
    (hd : d≤N) (hc : c≤N) :
    2*(104*(a+1)^2)+104*(b+c+a*d+1)^2+1 ≤ 1000*(N+2*A+B+1+1)^4:=by
  let T:=N+2*A+B+1
  have he : a≤T := by dsimp [T];omega
  have ht : d≤T := by dsimp [T];omega
  have hs0 : b+c≤T := by dsimp [T];omega
  have hs : b+c+a*d+1≤(T+1)^2:=by
    have hm:=Nat.mul_le_mul he ht
    nlinarith only [hs0,hm]
  have hh:=Nat.pow_le_pow_left hs 2
  have hh':=Nat.pow_le_pow_left (show a+1≤T+1 by omega) 2
  have hp4 : ((T+1)^2)^2=(T+1)^4:=by ring
  rw [hp4] at hh
  have h24 : (T+1)^2≤(T+1)^4:=Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 1≤(T+1)^4:=Nat.one_le_pow _ _ (Nat.succ_pos _)
  have h2:=(hh'.trans h24)
  change _ ≤ 1000*(T+1)^4
  omega
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeControlBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

namespace NodeCircuit

def primeBound (w : ℕ) := 49*w+10+rootWidth w+primalityBound w
def guardBound (w : ℕ) := 216*w*w+250*w+45
def quotientBound (w : ℕ) := 216*w*w+56*w+6
def splitBound (s w : ℕ) := ((s+1)*w)*(((s+1)*w)*(quotientBound w+(s+1)*w*w))
def nextBound (s w : ℕ) := 97*w+21+primeBound w+(s+1)*w*w+guardBound w+
  splitBound s w+21*((s+1)*w)

end NodeCircuit
end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeStateBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic.NodeStateCircuit
open BooleanNetwork

def outputBound (s w : ℕ) :=
  NodeCircuit.primeBound w+8*w+97*w+21+(s+1)*w*(NodeCircuit.primeBound w+8*w)+7*((s+1)*w)
def stepBound (s w : ℕ) := NodeCircuit.nextBound s w+outputBound s w+
  (97*w+21+NodeCircuit.primeBound w+NodeCircuit.guardBound w+9)

end ExactQuantumFactoring.BitArithmetic.NodeStateCircuit


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TrialControlEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.TrialControlEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission OrderTrial
variable {α : Type} {ea : α→List Bool} {k w n : α→ℕ}
def decodeEquiv : Fin 4 ≃ DecodeVar where
  toFun := ![.den,.num,.residue,.coin]
  invFun | .den=>0 | .num=>1 | .residue=>2 | .coin=>3
  left_inv i:=by fin_cases i <;> rfl
  right_inv i:=by cases i <;> rfl
end ExactQuantumFactoring.TrialControlEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_QuarterRetentionEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
def unitEquiv : Fin 1 ≃ Unit where
  toFun := fun _=>()
  invFun := fun _=>0
  left_inv i:=by exact Subsingleton.elim ..
  right_inv i:=by exact Subsingleton.elim ..
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RationalHeightResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring

/-- Bit-length bounds for exact normalized rational constants appearing in the
emitted circuit. These are not bounds on their exponentially large values. -/
def RatHeightPoly (a : ℕ → ℚ) : Prop :=
  PolyBound (fun n => (a n).num.natAbs.size) ∧ PolyBound (fun n => (a n).den.size)
end ExactQuantumFactoring

end



end OAI
end


