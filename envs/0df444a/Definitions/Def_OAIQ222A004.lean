-- Prove2me | Definitions.Def_OAIQ222A004
-- name    : OAIQ222A004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:09:43.031235+00:00
-- url     : https://prove2.me/theorems/7c16dc9a-5332-467c-9683-d40e86779f7c
-- title:
--   Definitions bundle OAIQ222A004 of the split of OpenAI, Exact quantum factoring over a fixed finite gate set (result family 279)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ExactQuantumFactoring.exact_quantum_factoring`, carved from OpenAI's openai/math development (OpenAI, *Exact quantum factoring over a fixed finite gate set (result family 279)*, OpenAI Math Release, September 25, 2026, result family 279, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 686 declarations of OpenAI's Lean: 615 definitions, 3 inductive types or structures, 6 instances and 62 theorems. The definitions and types are `OAI.ExactQuantumFactoring.AIGNetworkEmission.Emission.ultPackP`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.emitted`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.failed`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.isDone`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.isPrime`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.isProper`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.next`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.pack`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.popped`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.quotient`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeCircuit.split`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.bad`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.emission`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.nextBad`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.nextOutput`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.nextPending`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.nodeInput`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.old`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.output`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pack`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.pending`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.step`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.supplied`, `OAI.ExactQuantumFactoring.BitArithmetic.NodeStateCircuit.top`, `OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.compareStep`, `OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.headNet`, `OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.insertNet`, `OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.keepHead`, `OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.layout`, `OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.sortNet`, `OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.tailNet`, `OAI.ExactQuantumFactoring.BitArithmetic.add`, `OAI.ExactQuantumFactoring.BitArithmetic.addMod`, `OAI.ExactQuantumFactoring.BitArithmetic.aksBranch`, `OAI.ExactQuantumFactoring.BitArithmetic.aksStaticBranch`, `OAI.ExactQuantumFactoring.BitArithmetic.allCongruences`, `OAI.ExactQuantumFactoring.BitArithmetic.arrayConstant`, `OAI.ExactQuantumFactoring.BitArithmetic.boundedRootNet`, `OAI.ExactQuantumFactoring.BitArithmetic.candidateBits`, `OAI.ExactQuantumFactoring.BitArithmetic.candidateProduct` and 578 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `QuantumFactoring_AIGBitArithmeticEmission`, `QuantumFactoring_AKSNetworks`, `QuantumFactoring_ArithmeticPredicates`, `QuantumFactoring_BinLabelCircuit`, `QuantumFactoring_BitArithmetic`, `QuantumFactoring_BitArithmeticDivision`, `QuantumFactoring_BitStackBoundedPrime`, `QuantumFactoring_BooleanFold`, `QuantumFactoring_BoundedAKS`, `QuantumFactoring_BoundedStack`, `QuantumFactoring_CanonicalResidueCircuit`, `QuantumFactoring_CanonicalTransition`, `QuantumFactoring_CanonicalWords`, `QuantumFactoring_CircuitEmissionBasic`, `QuantumFactoring_CircuitEmissionEncoding`, `QuantumFactoring_CircuitEmissionModel`, `QuantumFactoring_CircuitPreparationEmission`, `QuantumFactoring_CircuitProgramEmission`, `QuantumFactoring_CleanPermutationEmission`, `QuantumFactoring_ClosedLevelCircuit`, `QuantumFactoring_CompletedOrderSlots`, `QuantumFactoring_CompletionPredicateCircuit`, `QuantumFactoring_ComponentPhiCircuit`, `QuantumFactoring_ContinuedFractionCircuit`, `QuantumFactoring_ControlledTranslation`, `QuantumFactoring_CyclicCircuit`, `QuantumFactoring_CyclicConstants`, `QuantumFactoring_CyclicPowerCircuit`, `QuantumFactoring_CyclicTestCircuit`, `QuantumFactoring_DescendingFilterEmission`, `QuantumFactoring_DistinctProductCircuit`, `QuantumFactoring_DyadicCompletion`, `QuantumFactoring_EmissionFurther`, `QuantumFactoring_ExpressionPostfix`, `QuantumFactoring_ExpressionPredicates`, `QuantumFactoring_ExpressionTemplateCircuit`, `QuantumFactoring_ExpressionTemplateEmission`, `QuantumFactoring_ExpressionTokenProcedure`, `QuantumFactoring_FactorGuess`, `QuantumFactoring_FactorVerifier`, `QuantumFactoring_FactoringCircuit`, `QuantumFactoring_FactoringInputLayout`, `QuantumFactoring_FixedSplit`, `QuantumFactoring_FlatLookupCircuit`, `QuantumFactoring_GcdCircuit`, `QuantumFactoring_HardFilterCircuit`, `QuantumFactoring_HornerEncoding`, `QuantumFactoring_InitialOrderState`, `QuantumFactoring_LabelRecoveryCircuit`, `QuantumFactoring_LabelValidationCircuit`, `QuantumFactoring_ListSamplerCircuit`, `QuantumFactoring_ListSamplerEmission`, `QuantumFactoring_ListTransition`, `QuantumFactoring_MachineInitialization`, `QuantumFactoring_MinimumCandidateCircuit`, `QuantumFactoring_ModularMultiply`, `QuantumFactoring_ModularPower`, `QuantumFactoring_NativeAIGModel`, `QuantumFactoring_NativeAIGShift`, `QuantumFactoring_NativeAIGVector`, `QuantumFactoring_NaturalExpressionCircuit`, `QuantumFactoring_NetworkAt`, `QuantumFactoring_NetworkCanonicalEmission`, `QuantumFactoring_NetworkEmissionBasic`, `QuantumFactoring_NetworkEmissionWords`, `QuantumFactoring_NetworkFoldChoiceEmission`, `QuantumFactoring_NetworkListEmission`, `QuantumFactoring_NetworkLoopEmission`, `QuantumFactoring_NetworkResizeEmission`, `QuantumFactoring_NetworkSequenceEmission`, `QuantumFactoring_NetworkStackCompiler`, `QuantumFactoring_NodeControlBounds`, `QuantumFactoring_NodeControlCircuit`, `QuantumFactoring_NodeProgress`, `QuantumFactoring_NodeSplitMachine`, `QuantumFactoring_NodeStateCircuit`, `QuantumFactoring_NodeVerifiedCircuit`, `QuantumFactoring_OrderCandidateLaw`, `QuantumFactoring_OrderSampleCircuit`, `QuantumFactoring_OrderSamplerMass`, `QuantumFactoring_OrderTransition`, `QuantumFactoring_ParallelPreparation`, `QuantumFactoring_PerfectPowerCircuit`, `QuantumFactoring_PhysicalCompletionOutput`, `QuantumFactoring_PhysicalDataLog`, `QuantumFactoring_PhysicalListNetworks`, `QuantumFactoring_PhysicalListSlots`, `QuantumFactoring_PhysicalMachine`, `QuantumFactoring_PhysicalMachineMass`, `QuantumFactoring_PhysicalNodeKernel`, `QuantumFactoring_PhysicalNodeLaunch`, `QuantumFactoring_PhysicalNodeOutput`, `QuantumFactoring_PhysicalOrderDecoder`, `QuantumFactoring_PhysicalOrderNetworks`, `QuantumFactoring_PhysicalOrderSlots`, `QuantumFactoring_PhysicalSplit`, `QuantumFactoring_PhysicalSplitDecoder`, `QuantumFactoring_PhysicalSplitLaunch`, `QuantumFactoring_PhysicalTreeCompletion`, `QuantumFactoring_PhysicalTreeLaunch`, `QuantumFactoring_PhysicalTreeMachine`, `QuantumFactoring_PhysicalTreeMass`, `QuantumFactoring_PhysicalTreeQueue`, `QuantumFactoring_PhysicalTrialLaw`, `QuantumFactoring_PrimeComponentCircuit`, `QuantumFactoring_QuarterPreparation`, `QuantumFactoring_RawTrialDecoder`, `QuantumFactoring_RawTrialFields`, `QuantumFactoring_RawTrialLabelCircuit`, `QuantumFactoring_RetainedCanonical`, `QuantumFactoring_RetainedComponentOrder`, `QuantumFactoring_RetainedFavorable`, `QuantumFactoring_RetainedFavorableCount`, `QuantumFactoring_RetainedListDummy`, `QuantumFactoring_RetainedListFilter`, `QuantumFactoring_RetainedNodeFilter`, `QuantumFactoring_RetainedOrderFilter`, `QuantumFactoring_RetainedQuarterFilter`, `QuantumFactoring_RetainedSplitFilter`, `QuantumFactoring_RetainedTable`, `QuantumFactoring_RetainedTotient`, `QuantumFactoring_RetainedTreeFilter`, `QuantumFactoring_RetentionCircuit`, `QuantumFactoring_RetrospectiveCircuit`, `QuantumFactoring_RetrospectiveLists`, `QuantumFactoring_RetrospectiveNode`, `QuantumFactoring_RetrospectiveSlots`, `QuantumFactoring_RetrospectiveTree`, `QuantumFactoring_RootCircuit`, `QuantumFactoring_RuntimeListPreparation`, `QuantumFactoring_SamplerDecodeCircuit`, `QuantumFactoring_SamplerLabels`, `QuantumFactoring_SortingCircuit`, `QuantumFactoring_SplitCandidate`, `QuantumFactoring_SplitHistoryAccess`, `QuantumFactoring_StaticPredicates`, `QuantumFactoring_SuppliedDivisorCircuit`, `QuantumFactoring_TableDirectPhi`, `QuantumFactoring_TableFavorableCount`, `QuantumFactoring_TableLevelCircuit`, `QuantumFactoring_TableOrderCircuit`, `QuantumFactoring_TableTotientCircuit`, `QuantumFactoring_TensorPreparation`, `QuantumFactoring_TensorWiring`, `QuantumFactoring_ThresholdRetention`, `QuantumFactoring_TotientCircuit`, `QuantumFactoring_TransitionNetworks`, `QuantumFactoring_TransitionWords`, `QuantumFactoring_TreeAmplified`, `QuantumFactoring_TreeHistoryAccess`, `QuantumFactoring_TreeInitialization`, `QuantumFactoring_TreePadding`, `QuantumFactoring_TreePhysicalPreparation`, `QuantumFactoring_TreeQuarterPhysical`, `QuantumFactoring_TreeReadOnly`, `QuantumFactoring_TreeReadout`, `QuantumFactoring_TreeRootOutput`, `QuantumFactoring_TreeTableEmission`, `QuantumFactoring_TrialControlCircuit`, `QuantumFactoring_TrialGuessLaw`, `QuantumFactoring_TrialRawPreparation`, `QuantumFactoring_TriangularCircuit`, `QuantumFactoring_TriangularPreparation`, `QuantumFactoring_TwoAdicCircuit`, `QuantumFactoring_UniversalSplit`, `QuantumFactoring_VerifiedTableOrder`, `QuantumFactoring_VerifiedTreeBounds`, `QuantumFactoring_WideSplitCircuit`, `QuantumFactoring_WordBlocks`, `QuantumFactoring_WordNetworks`, `QuantumFactoring_WordSumCircuit`, `QuantumFactoring_ZeroOutside`.
--
--   **Imports.** It imports the published bundle `Def_ExactQuantumFactoring`; the bundles `OAIQ222A002` and `OAIQ222A003` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.ExactQuantumFactoring.NetworkEmission.NetEmits.factorVerifier`, `OAI.ExactQuantumFactoring.NetworkEmission.NetEmits.tableFavorableCount`, `OAI.ExactQuantumFactoring.NodeMachine.retainedOrderFilter_exact`, `OAI.ExactQuantumFactoring.NodeStateEmission.step`, `OAI.ExactQuantumFactoring.OrderTrial.orderResult_mass`, `OAI.ExactQuantumFactoring.PhysicalNodeEmission.kernelInitial`, `OAI.ExactQuantumFactoring.PhysicalNodeEmission.update`, `OAI.ExactQuantumFactoring.PhysicalNode.decoded_value`, `OAI.ExactQuantumFactoring.PhysicalOrderEmission.result`, `OAI.ExactQuantumFactoring.PhysicalSplitEmission.actualOrder`, `OAI.ExactQuantumFactoring.PhysicalSplitEmission.program`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.hardOn`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.lastNode`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.listFilterVars`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.machineWidth`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.orderFilterVars`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.paddedFlag`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.paddedHistory`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.paddedPad`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.previous`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.program`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.quarterCoin`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.quarterGuessFlag`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.quarterOrd`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.quarterOutput`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.quarterProgram`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.quarterRare`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.quarterWidth`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.retainedCanonicalList`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.retainedComponentOrder`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.retainedGoodList`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.retainedOrder`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.retainedOrderPhi`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.retainedSplitFilter`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.rowQuery`, `OAI.ExactQuantumFactoring.PhysicalTree.accepted_iff_passed`, `OAI.ExactQuantumFactoring.PhysicalTree.finalCircuit_resources`, `OAI.ExactQuantumFactoring.PhysicalTree.finalCircuit_spec`, `OAI.ExactQuantumFactoring.PhysicalTree.quarterFlag_eval`, `OAI.ExactQuantumFactoring.PhysicalTree.treePrefixFilter_passed` and `OAI.ExactQuantumFactoring.TrialControlEmission.accept`; the proofs of `OAI.ExactQuantumFactoring.Completion.orderSuccess_lower`, `OAI.ExactQuantumFactoring.NetworkEmission.NetEmits.factorVerifier`, `OAI.ExactQuantumFactoring.NetworkEmission.NetEmits.tableFavorableCount`, `OAI.ExactQuantumFactoring.NodeMachine.retainedOrderFilter_exact`, `OAI.ExactQuantumFactoring.NodeStateEmission.step`, `OAI.ExactQuantumFactoring.OrderTrial.orderResult_mass`, `OAI.ExactQuantumFactoring.PhysicalNodeEmission.kernelInitial`, `OAI.ExactQuantumFactoring.PhysicalNodeEmission.update`, `OAI.ExactQuantumFactoring.PhysicalNode.decoded_value`, `OAI.ExactQuantumFactoring.PhysicalOrderEmission.result`, `OAI.ExactQuantumFactoring.PhysicalSplitEmission.actualOrder`, `OAI.ExactQuantumFactoring.PhysicalSplitEmission.program`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.hardOn`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.lastNode`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.listFilterVars`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.machineWidth`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.orderFilterVars`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.paddedFlag`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.paddedHistory`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.paddedPad`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.previous`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.program`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.quarterCoin`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.quarterGuessFlag`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.quarterOrd`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.quarterOutput`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.quarterProgram`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.quarterRare`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.quarterWidth`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.retainedCanonicalList`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.retainedComponentOrder`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.retainedGoodList`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.retainedOrder`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.retainedOrderPhi`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.retainedSplitFilter`, `OAI.ExactQuantumFactoring.PhysicalTreeEmission.rowQuery`, `OAI.ExactQuantumFactoring.PhysicalTree.accepted_iff_passed`, `OAI.ExactQuantumFactoring.PhysicalTree.finalCircuit_resources`, `OAI.ExactQuantumFactoring.PhysicalTree.finalCircuit_spec`, `OAI.ExactQuantumFactoring.PhysicalTree.quarterFlag_eval`, `OAI.ExactQuantumFactoring.PhysicalTree.treePrefixFilter_passed`, `OAI.ExactQuantumFactoring.TrialControlEmission.accept` and `OAI.ExactQuantumFactoring.exact_quantum_factoring`.
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
import Definitions.Def_OAIQ222A002
import Definitions.Def_OAIQ222A003

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std Sat
def Rel {n : ℕ} (r : Graph) (g : AIG (Fin n)) : Prop :=
  r.decls=g.decls.toList.map eraseDecl ∧
  ∀ k,lookup k r.cache=g.cache.val[nativeKey (n:=n) k]?

def EPRel {n : ℕ} (r : Graph × Ref) (e : AIG.Entrypoint (Fin n)) : Prop :=
  Rel r.1 e.aig ∧ r.2=(e.ref.gate,e.ref.invert)

end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat

def VecRel {n w : ℕ} (r : Graph×List Ref) (v : AIG.RefVecEntry (Fin n) w) : Prop :=
  Rel r.1 v.aig ∧ r.2=eraseVec v.vec

end ExactQuantumFactoring.NativeAIG

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

def band (a b : Data) : Data:=comp (pair a b) (node 2 (.conj 0 1))
end ExactQuantumFactoring.NetworkEmission

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
open AIGCompiler BooleanNetwork

def add (w : ℕ) : BooleanNetwork (w+w) w :=
  let res := blastAdd (inputs (w+w)).1 (binaryInputs w)
  compileVec res.aig res.vec

def mul (w : ℕ) : BooleanNetwork (w+w) w :=
  let res := blastMul (inputs (w+w)).1 (binaryInputs w)
  compileVec res.aig res.vec

lemma add_count (w : ℕ) : (add w).net.count ≤ 86*w+6 := by
  have h := compileVec_count (blastAdd (inputs (w+w)).1 (binaryInputs w)).aig
    (blastAdd (inputs (w+w)).1 (binaryInputs w)).vec
  have hs := AIGBounds.add_size (inputs (w+w)).1 (binaryInputs w)
  rw [inputs_size] at hs
  dsimp only [add]
  omega

lemma mul_count (w : ℕ) : (mul w).net.count ≤ 90*w*w+14*w+6 := by
  have h := compileVec_count (blastMul (inputs (w+w)).1 (binaryInputs w)).aig
    (blastMul (inputs (w+w)).1 (binaryInputs w)).vec
  have hs := AIGBounds.mul_size (inputs (w+w)).1 (binaryInputs w)
  rw [inputs_size] at hs
  dsimp only [mul]
  nlinarith

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BitArithmeticDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast
open AIGCompiler BooleanNetwork

lemma sub_count (w : ℕ) : (sub w).net.count ≤ 158*w+6 := by
  have h := compileVec_count (blastSub (inputs (w+w)).1 (binaryInputs w)).aig
    (blastSub (inputs (w+w)).1 (binaryInputs w)).vec
  have hs := AIGBounds.sub_size (inputs (w+w)).1 (binaryInputs w)
  rw [inputs_size] at hs
  dsimp only [sub]
  nlinarith

def div (w : ℕ) : BooleanNetwork (w+w) w :=
  let res := blastUdiv (inputs (w+w)).1 (binaryInputs w)
  compileVec res.aig res.vec

def mod (w : ℕ) : BooleanNetwork (w+w) w :=
  let res := blastUmod (inputs (w+w)).1 (binaryInputs w)
  compileVec res.aig res.vec

lemma mod_count (w : ℕ) : (mod w).net.count ≤ 216*w*w+56*w+6 := by
  have h := compileVec_count (blastUmod (inputs (w+w)).1 (binaryInputs w)).aig
    (blastUmod (inputs (w+w)).1 (binaryInputs w)).vec
  have hs := AIGBounds.mod_size (inputs (w+w)).1 (binaryInputs w)
  rw [inputs_size] at hs
  dsimp only [mod]
  nlinarith

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_WordNetworks
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
namespace BitArithmetic
open BooleanNetwork

lemma wordConstant_count {n w : ℕ} (v : BitVec w) :
    (wordConstant (n := n) v).net.count = w := by
  simp [wordConstant]

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ArithmeticPredicates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open Std.Sat Std.Tactic.BVDecide
open AIGCompiler BooleanNetwork

lemma ult_count (w : ℕ) : (ult w).net.count ≤ 48*w+8 := by
  have h := compile_count (BVPred.mkUlt (inputs (w+w)).1 (binaryInputs w)).aig
    (m := 1) (fun _ => (BVPred.mkUlt (inputs (w+w)).1 (binaryInputs w)).ref)
  have hs := AIGBounds.ult_size (inputs (w+w)).1 (binaryInputs w)
  rw [inputs_size] at hs
  dsimp only [ult]
  omega

lemma wordLt_count {n w : ℕ} (a b : BooleanNetwork n w) :
    (wordLt a b).net.count ≤ a.net.count+b.net.count+48*w+8 := by
  simp only [wordLt,count_comp,count_pair]
  have := ult_count w
  omega

def wordLe {n w : ℕ} (a b : BooleanNetwork n w) : BooleanNetwork n 1 :=
  (wordLt b a).bnot

/-- Static natural exponent, with retained accumulator and no repeated
construction of earlier expressions. This circuit has O(e w²) Boolean nodes. -/
def staticPowerStep (w : ℕ) : BooleanNetwork (w+w) (w+w) :=
  (select (Fin.castAdd w)).pair (mul w)

def staticPower (w e : ℕ) : BooleanNetwork w w :=
  ((select id).pair (wordConstant (BitVec.ofNat w 1))).comp
    (((staticPowerStep w).iterate e).rewire (Fin.natAdd w))

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NativeAIGShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast

def shiftLoop : ℕ→List Ref→ℕ→ℕ→List Ref→List Ref
  | 0,_,_,_,out=>out
  | k+1,xs,d,i,out=>shiftLoop k xs d (i+1) (out++[shiftBit xs d i])
end ExactQuantumFactoring.NativeAIG

end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AIGBitArithmeticEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.AIGNetworkEmission
open Std.Sat Std.Tactic.BVDecide.BVExpr.bitblast
open BitStackProgram BitStackProgram.Procedure NetworkEmission

namespace Emission
noncomputable def ultPackP : Procedure unaryCode packCode ultPack:=by
  let width:=unaryAdd.comp ((identity unaryCode).pair (identity unaryCode))
  let ds:=NativeAIG.Emission.decls.comp ((first NativeAIG.graphCode NativeAIG.refCode).comp inputUltP)
  let ref:=(second NativeAIG.graphCode NativeAIG.refCode).comp inputUltP
  let refs:=(listCons NativeAIG.refCode).comp (ref.pair (Procedure.constant _ (listCode NativeAIG.refCode) []))
  exact compilePackP.comp ((width.pair ds).pair refs)
end Emission
end ExactQuantumFactoring.AIGNetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BooleanFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BooleanNetwork
open scoped BigOperators

def all {n : ℕ} : List (BooleanNetwork n 1) → BooleanNetwork n 1
  | [] => constant true
  | c::cs => c.band (all cs)

end ExactQuantumFactoring.BooleanNetwork


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ModularMultiply
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

/-- Full double-width product followed by full double-width remainder, with no
word overflow. The narrow remainder is valid because the modulus is a word. -/
def mulMod {n w : ℕ} (a b m : BooleanNetwork n w) : BooleanNetwork n w :=
  let p := ((a.comp (padRight w w)).pair (b.comp (padRight w w))).comp (mul (w+w))
  ((p.pair (m.comp (padRight w w))).comp (mod (w+w))).rewire (Fin.castAdd w)

lemma mulMod_count {n w : ℕ} (a b m : BooleanNetwork n w) :
    (mulMod a b m).net.count ≤
      a.net.count + b.net.count + m.net.count + (1224*w*w+143*w+12) := by
  have h₁ := mul_count (w+w)
  have h₂ := mod_count (w+w)
  simp only [mulMod, count_rewire, count_comp, count_pair, count_padRight]
  nlinarith

lemma wordMux_count {n w : ℕ} (c : BooleanNetwork n 1) (a b : BooleanNetwork n w) :
    (wordMux c a b).net.count = c.net.count+a.net.count+b.net.count+7*w := by
  simp [wordMux, count_comp, count_pair, Nat.mul_comm]

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ModularPower
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork
open scoped BigOperators

def powerNew (w : ℕ) {b : ℕ} (i : Fin b) : BooleanNetwork (powerWidth w b) w :=
  let sq := mulMod (powerAcc w b) (powerAcc w b) (powerModulus w b)
  wordMux (powerBit w i) (mulMod sq (powerBase w b) (powerModulus w b)) sq

def powerStep (w : ℕ) {b : ℕ} (i : Fin b) :
    BooleanNetwork (powerWidth w b) (powerWidth w b) :=
  (select (Fin.castAdd w)).pair (powerNew w i)

lemma powerNew_count (w : ℕ) {b : ℕ} (i : Fin b) :
    (powerNew w i).net.count ≤ 3*(1224*w*w+143*w+12)+7*w := by
  have h₁ := mulMod_count (powerAcc w b) (powerAcc w b) (powerModulus w b)
  have h₂ := mulMod_count
    (mulMod (powerAcc w b) (powerAcc w b) (powerModulus w b))
    (powerBase w b) (powerModulus w b)
  have h₀ : (powerAcc w b).net.count = 0 ∧ (powerModulus w b).net.count = 0 ∧
      (powerBase w b).net.count = 0 := ⟨rfl,rfl,rfl⟩
  simp only [h₀.1, h₀.2.1, h₀.2.2, zero_add, add_zero] at h₁ h₂
  simp only [powerNew, wordMux_count, powerBit, count_bit, zero_add]
  omega

lemma powerStep_count (w : ℕ) {b : ℕ} (i : Fin b) :
    (powerStep w i).net.count ≤ 3672*w*w+436*w+36 := by
  have h := powerNew_count w i
  simp only [powerStep, count_pair, count_select, zero_add]
  nlinarith

/-- Horner value processes the actual physical data bits from low wire to high
wire, matching the reversed input convention of the triangular transform. -/
def horner {b : ℕ} (e : Basis b) : (k : ℕ) → k ≤ b → ℕ
  | 0, _ => 0
  | k+1, h => 2*horner e k (by omega) + (e ⟨k,by omega⟩).toNat

def powerPrefix (w b : ℕ) : (k : ℕ) → k ≤ b → BooleanNetwork (powerWidth w b) (powerWidth w b)
  | 0, _ => select id
  | k+1, h => (powerPrefix w b k (by omega)).comp (powerStep w ⟨k,by omega⟩)

lemma powerPrefix_count (w b k : ℕ) (hk : k ≤ b) :
    (powerPrefix w b k hk).net.count ≤ k*(3672*w*w+436*w+36) := by
  induction k with
  | zero => simp [powerPrefix]
  | succ k ih =>
    have h := powerStep_count w (⟨k,by omega⟩ : Fin b)
    simp only [powerPrefix, count_comp]
    have hh := ih (by omega)
    nlinarith

/-- The complete bounded binary-power network. Inputs remain available for
copying; the result is a separate output word. -/
def modularPower (w b : ℕ) : BooleanNetwork ((w+w)+b) w :=
  ((select id).pair (wordConstant (BitVec.ofNat w 1))).comp
    ((powerPrefix w b b le_rfl).rewire (Fin.natAdd ((w+w)+b)))

lemma modularPower_count (w b : ℕ) :
    (modularPower w b).net.count ≤ w+b*(3672*w*w+436*w+36) := by
  have h := powerPrefix_count w b b le_rfl
  simp only [modularPower,count_comp,count_pair,count_select,wordConstant_count,
    count_rewire,zero_add]
  omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_HornerEncoding
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_eval _root_.OAI.ExactQuantumFactoring.BitArithmetic.decodeCyclic_coeff _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

/-- The physical input word reversal is an explicit wire permutation. -/
def reverseBits (b : ℕ) : Equiv.Perm (Basis b) where
  toFun x := x ∘ Fin.rev
  invFun x := x ∘ Fin.rev
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

lemma Triangular.inputNumber_reverse {b : ℕ} (x : Basis b) :
    inputNumber x = (bitsValue (reverseBits b x)).toNat := by
  rw [bitsValue_toNat]
  unfold inputNumber
  rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin b))]
  apply Finset.sum_congr rfl
  intro i _
  change 2^(b-1-(b-(i.val+1)))*(x (Fin.rev i)).toNat =
    2^i.val*(x (Fin.rev i)).toNat
  have he : b-1-(b-(i.val+1)) = i.val := by have := i.isLt; omega
  rw [he]

lemma Triangular.inputNumber_lt {b : ℕ} (x : Basis b) : inputNumber x < 2^b := by
  rw [inputNumber_reverse]
  exact (bitsValue _).isLt

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_StaticPredicates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

def equalOn {n w : ℕ} (a b : BooleanNetwork n w) : BooleanNetwork n 1 :=
  (a.pair b).comp (wordEq w)

def constMod (w d : ℕ) : BooleanNetwork w w :=
  ((select id).pair (wordConstant (BitVec.ofNat w d))).comp (mod w)

def dividesNet (w d : ℕ) : BooleanNetwork w 1 :=
  equalOn (constMod w d) (wordConstant (BitVec.ofNat w 0))

/-- Static modulus and exponent; exponent wiring is reversed explicitly. -/
def constPowMod (w s j : ℕ) : BooleanNetwork w w :=
  (((select id).pair (wordConstant (BitVec.ofNat w s))).pair
    ((wordConstant (BitVec.ofNat w j)).rewire Fin.rev)).comp (modularPower w w)

def powerOneNet (w s j : ℕ) : BooleanNetwork w 1 :=
  equalOn (constPowMod w s j) (wordConstant (BitVec.ofNat w 1))

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_AKSNetworks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

def orderTests (w s k : ℕ) : BooleanNetwork w 1 :=
  all (List.ofFn (fun i : Fin k => (powerOneNet w s (i.val+1)).bnot))

def properDivisor (w d : ℕ) : BooleanNetwork w 1 :=
  (dividesNet w d).band (wordLt (wordConstant (BitVec.ofNat w d)) (select id))

def noSmallDivisor (w B : ℕ) : BooleanNetwork w 1 :=
  all (List.ofFn (fun i : Fin (B-1) => (properDivisor w (i.val+2)).bnot))

end ExactQuantumFactoring.BitArithmetic


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
open BooleanNetwork

def rootNext (w k : ℕ) : BooleanNetwork (w+w) w :=
  ((rootGuess w).pair (wordConstant (BitVec.ofNat w (2^k)))).comp (add w)

def rootNew (w e k : ℕ) : BooleanNetwork (w+w) w :=
  wordMux (wordLe ((rootNext w k).comp (staticPower w e)) (rootModulus w))
    (rootNext w k) (rootGuess w)

def rootStep (w e k : ℕ) : BooleanNetwork (w+w) (w+w) :=
  (rootModulus w).pair (rootNew w e k)

def rootPrefix (w e : ℕ) : ℕ → BooleanNetwork (w+w) (w+w)
  | 0 => select id
  | k+1 => (rootStep w e k).comp (rootPrefix w e k)

def boundedRootNet (n e : ℕ) : BooleanNetwork (rootWidth n) (rootWidth n) :=
  ((select id).pair (wordConstant (BitVec.ofNat (rootWidth n) 0))).comp
    ((rootPrefix (rootWidth n) e n).rewire (Fin.natAdd (rootWidth n)))

end ExactQuantumFactoring.BitArithmetic


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
open BooleanNetwork

def euclidStep (w : ℕ) : BooleanNetwork (w+w) (w+w) :=
  let z := wordConstant (BitVec.ofNat w 0)
  let done := equalOn (rootGuess w) z
  (wordMux done (rootModulus w) (rootGuess w)).pair
    (wordMux done z (mod w))

def euclidPrefix (w : ℕ) : ℕ → BooleanNetwork (w+w) (w+w)
  | 0 => select id
  | k+1 => (euclidStep w).comp (euclidPrefix w k)

def gcdNet (w : ℕ) : BooleanNetwork (w+w) w :=
  (euclidPrefix w (2*w)).comp (rootModulus w)

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
open BooleanNetwork BitArithmetic

namespace BitArithmetic

def halfWord {k w : ℕ} (d : BooleanNetwork k w) : BooleanNetwork k w :=
  (d.pair (wordConstant (BitVec.ofNat w 2))).comp (div w)

end BitArithmetic
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
open BooleanNetwork
open OrderTrial

def cfProduct (w : ℕ) : BooleanNetwork (w+(w+w)) w :=
  (((cfHead w).pair (cfP w)).comp (mul w)).pair (cfQ w) |>.comp (add w)
def cfCombine (w : ℕ) : BooleanNetwork (w+(w+w)) (w+w) :=
  let z := equalOn (cfP w) (wordConstant (BitVec.ofNat w 0))
  (wordMux z (cfHead w) (cfProduct w)).pair
    (wordMux z (wordConstant (BitVec.ofNat w 1)) (cfP w))

def convergentNet (w : ℕ) : ℕ → BooleanNetwork (w+w) (w+w)
  | 0 => (div w).pair (wordConstant (BitVec.ofNat w 1))
  | k+1 =>
    ((div w).pair ((rootGuess w).pair (mod w))).comp
      ((cfHead w).pair ((cfTail w).comp (convergentNet w k))) |>.comp (cfCombine w)

end ExactQuantumFactoring.BitArithmetic


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
open BooleanNetwork BitArithmetic

namespace BitArithmetic

def natSubOn {k w : ℕ} (a b : BooleanNetwork k w) : BooleanNetwork k w :=
  wordMux (wordLe b a) ((a.pair b).comp (sub w)) (wordConstant (BitVec.ofNat w 0))

end BitArithmetic
namespace NatExpr
variable {v : Type*} {k w : ℕ}

def compile (vars : v → BooleanNetwork k w) : NatExpr v → BooleanNetwork k w
  | .var i => vars i
  | .const c => wordConstant (BitVec.ofNat w c)
  | .add a b => ((compile vars a).pair (compile vars b)).comp (BitArithmetic.add w)
  | .mul a b => ((compile vars a).pair (compile vars b)).comp (BitArithmetic.mul w)
  | .sub a b => natSubOn (compile vars a) (compile vars b)
  | .div a b => ((compile vars a).pair (compile vars b)).comp (BitArithmetic.div w)
  | .mod a b => ((compile vars a).pair (compile vars b)).comp (BitArithmetic.mod w)
  | .iteLe a b c d => wordMux (wordLe (compile vars a) (compile vars b))
      (compile vars c) (compile vars d)

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
open BooleanNetwork BitArithmetic
namespace NatExpr
variable {v : Type*}

def template {k b : ℕ} (e : NatExpr v) (vars : v → BooleanNetwork k b) :
    BooleanNetwork k (e.templateWidth b) :=
  e.compile (fun i => (vars i).comp (resizeWord b (e.templateWidth b)))

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
open BooleanNetwork BitArithmetic
namespace NatExpr
variable {v : Type*}

/-- A total exact predicate compiler. All intermediate words are widened from
an explicit expression-derived bound, including on rejected inputs. -/
def isOne {k b : ℕ} (e : NatExpr v) (vars : v → BooleanNetwork k b) : BooleanNetwork k 1 :=
  equalOn (e.template vars) (wordConstant (BitVec.ofNat (e.templateWidth b) 1))
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
open BooleanNetwork BitArithmetic

def checkedConvergent {n w : ℕ} (i : ℕ) (Q B k : BooleanNetwork n w) : BooleanNetwork n (w+w) :=
  let conv := (k.pair Q).comp (convergentNet w i)
  let d := conv.comp (rootGuess w)
  let j := conv.comp (rootModulus w)
  let pass := binCheckExpr.isOne ![Q,B,k,d,j]
  (wordMux pass d (wordConstant (BitVec.ofNat w 0))).pair
    (wordMux pass j (wordConstant (BitVec.ofNat w 0)))

end ExactQuantumFactoring.OrderTrial


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
namespace Procedure
noncomputable def unaryPrime : Procedure unaryCode boolCode (fun n=>decide (Nat.Prime n)):=by
  let i:=(unaryToBits.comp (first unaryCode Nat.bits))
  let n:=second unaryCode Nat.bits
  let small:=binaryLt.comp (i.pair (constant _ Nat.bits 2))
  let nondvd:=boolNot.comp (binaryEq.comp ((binaryMod.comp (n.pair i)).pair (constant _ Nat.bits 0)))
  let test:=boolOr.comp (small.pair nondvd)
  let table:=tabulate (f:=fun n i=>decide (i<2) || !decide (n%i=0)) false test
  let all:=(boolListAll.comp table).comp ((identity unaryCode).pair unaryToBits)
  let large:=boolNot.comp (binaryLt.comp (unaryToBits.pair (constant unaryCode Nat.bits 2)))
  exact (boolAnd.comp (large.pair all)).congrFun (by
    intro n
    apply Bool.eq_iff_iff.mpr
    change ((!decide (n<2)) && ((List.range n).map (fun i=>decide (i<2) || !decide (n%i=0))).all id)=true ↔ _
    simp only [Bool.and_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,List.all_eq_true,List.mem_map,
      id_eq,decide_eq_true_eq]
    rw [Nat.prime_def_lt']
    constructor
    · rintro ⟨hn,h⟩
      refine ⟨by omega,?_⟩
      intro m hm hmn hd
      have ht:=h _ ⟨m,List.mem_range.mpr hmn,rfl⟩
      simp only [Bool.or_eq_true,decide_eq_true_eq,Bool.not_eq_true',decide_eq_false_iff_not] at ht
      exact ht.elim (by omega) (fun h=>h (Nat.dvd_iff_mod_eq_zero.mp hd))
    · rintro ⟨hn,h⟩
      refine ⟨by omega,?_⟩
      rintro b ⟨m,hm,rfl⟩
      simp only [Bool.or_eq_true,decide_eq_true_eq,Bool.not_eq_true',decide_eq_false_iff_not]
      by_cases hlt : m<2
      · exact Or.inl hlt
      · exact Or.inr (fun hz=>h m (by omega) (List.mem_range.mp hm) (Nat.dvd_iff_mod_eq_zero.mpr hz)))
end Procedure

end ExactQuantumFactoring.BitStackProgram
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
open BooleanNetwork
open scoped BigOperators

/-- One extra carry bit before reduction avoids overflow even on noncanonical
coefficient representatives; all arrays use exactly as many bits as specified. -/
def addMod {n w : ℕ} (a b m : BooleanNetwork n w) : BooleanNetwork n w :=
  let p := ((a.comp (padRight w 1)).pair (b.comp (padRight w 1))).comp (add (w+1))
  ((p.pair (m.comp (padRight w 1))).comp (mod (w+1))).rewire (Fin.castAdd 1)

/-- Linear-length modular accumulation, not a repeated expanded expression. -/
def sumMod {n w : ℕ} (m : BooleanNetwork n w) : List (BooleanNetwork n w) → BooleanNetwork n w
  | [] => wordConstant 0
  | a::as => addMod a (sumMod m as) m

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
open BooleanNetwork Primality
open scoped BigOperators

def cyclicTerm {n s w : ℕ} [NeZero s] (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (k i : Fin s) : BooleanNetwork n w :=
  mulMod (a.comp (blockNet s w i)) (b.comp (blockNet s w (k-i))) m

def cyclicMulNet {n s w : ℕ} [NeZero s] (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) : BooleanNetwork n (s*w) :=
  wordBlocks (fun k => sumMod m (List.ofFn (cyclicTerm a b m k)))

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality
open scoped BigOperators

def arrayConstant {n : ℕ} (s w : ℕ) (f : Fin s → ℕ) : BooleanNetwork n (s*w) :=
  wordBlocks (fun i => wordConstant (BitVec.ofNat w (f i)))

def cyclicOne {n : ℕ} (s w : ℕ) [NeZero s] : BooleanNetwork n (s*w) :=
  arrayConstant s w (fun i => if i=0 then 1 else 0)

def cyclicAddNet {n s w : ℕ} (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) : BooleanNetwork n (s*w) :=
  wordBlocks (fun i => addMod (a.comp (blockNet s w i)) (b.comp (blockNet s w i)) m)

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicPowerCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
attribute [-simp] _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality

def cyclicPack {s w b : ℕ} (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z : Basis (s*w)) : Basis (cyclicPowerWidth s w b) :=
  Fin.append (Fin.append (Fin.append a m) e) z

def cyclicMod (s w b : ℕ) : BooleanNetwork (cyclicPowerWidth s w b) w :=
  select (fun i => ((Fin.natAdd (s*w) i).castAdd b).castAdd (s*w))
def cyclicBit (s w : ℕ) {b : ℕ} (i : Fin b) : BooleanNetwork (cyclicPowerWidth s w b) 1 :=
  bit ((Fin.natAdd (s*w+w) i).castAdd (s*w))

@[simp] lemma cyclicBase_eval {s w b : ℕ} (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z : Basis (s*w)) : (cyclicBase s w b).eval (cyclicPack a m e z)=a := by
  funext i
  simp only [cyclicBase,eval_select,Function.comp_apply,cyclicPack,Fin.append_left]
@[simp] lemma cyclicMod_eval {s w b : ℕ} (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z : Basis (s*w)) : (cyclicMod s w b).eval (cyclicPack a m e z)=m := by
  funext i
  simp only [cyclicMod,eval_select,Function.comp_apply,cyclicPack,Fin.append_left,Fin.append_right]
@[simp] lemma cyclicAcc_eval {s w b : ℕ} (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z : Basis (s*w)) : (cyclicAcc s w b).eval (cyclicPack a m e z)=z := by
  funext i
  simp only [cyclicAcc,eval_select,Function.comp_apply,cyclicPack,Fin.append_right]
@[simp] lemma cyclicBit_eval {s w b : ℕ} (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z : Basis (s*w)) (i : Fin b) : (cyclicBit s w i).eval (cyclicPack a m e z) 0=e i := by
  simp only [cyclicBit,eval_bit,cyclicPack,Fin.append_left,Fin.append_right]

def cyclicNew (s w : ℕ) [NeZero s] {b : ℕ} (i : Fin b) :
    BooleanNetwork (cyclicPowerWidth s w b) (s*w) :=
  let sq := cyclicMulNet (cyclicAcc s w b) (cyclicAcc s w b) (cyclicMod s w b)
  wordMux (cyclicBit s w i) (cyclicMulNet sq (cyclicBase s w b) (cyclicMod s w b)) sq

def cyclicStep (s w : ℕ) [NeZero s] {b : ℕ} (i : Fin b) :
    BooleanNetwork (cyclicPowerWidth s w b) (cyclicPowerWidth s w b) :=
  (select (Fin.castAdd (s*w))).pair (cyclicNew s w i)

def cyclicPrefix (s w b : ℕ) [NeZero s] : (k : ℕ) → k ≤ b →
    BooleanNetwork (cyclicPowerWidth s w b) (cyclicPowerWidth s w b)
  | 0,_ => select id
  | k+1,h => (cyclicPrefix s w b k (by omega)).comp (cyclicStep s w ⟨k,by omega⟩)

/-- n-bit repeated squaring in the coefficient array; no exponential polynomial
or algebraic root is part of the computation. -/
def cyclicPower (s w b : ℕ) [NeZero s] : BooleanNetwork ((s*w+w)+b) (s*w) :=
  ((select id).pair (cyclicOne s w)).comp
    ((cyclicPrefix s w b b le_rfl).rewire (Fin.natAdd ((s*w+w)+b)))

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CyclicTestCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality

def cyclicXNet {n : ℕ} (s w : ℕ) [NeZero s] : BooleanNetwork n (s*w) :=
  arrayConstant s w (fun i => if i=1 then 1 else 0)
def cyclicCNet {n : ℕ} (s w a : ℕ) [NeZero s] : BooleanNetwork n (s*w) :=
  arrayConstant s w (fun i => if i=0 then a else 0)

def cyclicPowerOn {n s w b : ℕ} [NeZero s] (a : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (e : BooleanNetwork n b) : BooleanNetwork n (s*w) :=
  ((a.pair m).pair e).comp (cyclicPower s w b)

/-- Literal 8s AKS congruence on s coefficient words, m in the input word. -/
def cyclicTest (s w a : ℕ) [NeZero s] : BooleanNetwork w 1 :=
  let m := select id
  let e := select Fin.rev
  let X := cyclicXNet s w
  let C := cyclicCNet s w a
  let lhs := cyclicPowerOn (cyclicAddNet X C m) m e
  let rhs := cyclicAddNet (cyclicPowerOn X m e) C m
  (lhs.pair rhs).comp (wordEq (s*w))

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
open BooleanNetwork

/-- Check a candidate root against the input integer, with its static exponent. -/
def rootCheck (w e : ℕ) : BooleanNetwork (w+w) 1 :=
  (wordLe (wordConstant (BitVec.ofNat w 2)) (rootGuess w)).band
    ((((rootGuess w).comp (staticPower w e)).pair (rootModulus w)).comp (wordEq w))

def exponentCheck (n e : ℕ) : BooleanNetwork (rootWidth n) 1 :=
  ((select id).pair (boundedRootNet n e)).comp (rootCheck (rootWidth n) e)

def perfectPowerNet (n : ℕ) : BooleanNetwork (rootWidth n) 1 :=
  any (List.ofFn (fun e : Fin (n+1) => if 2 ≤ e.val then exponentCheck n e.val else constant false))

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BoundedAKS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality

def allCongruences (s w : ℕ) [NeZero s] : BooleanNetwork w 1 :=
  all (List.ofFn (fun i : Fin (8*s) => cyclicTest s w (i.val+1)))

/-- The auxiliary modulus branch. The bounded small-divisor test is performed
before the congruences. Evaluating every modulus is a polynomial unrolling of
(the first qualifying modulus in) the manuscript's bounded search. -/
def aksBranch (n s : ℕ) [NeZero s] : BooleanNetwork (rootWidth n) 1 :=
  let w := rootWidth n
  ((dividesNet w s).bnot.band (orderTests w s (n^2))).band
    ((noSmallDivisor w (8*s)).band (allCongruences s w))

/-- The condition is on the compile-time parameter s≤n^8, not on the possibly
exponentially large input integer. Decidable primality here is a finite bounded
search; its generation-cost proof is separate from circuit size. -/
def aksStaticBranch (n s : ℕ) : BooleanNetwork (rootWidth n) 1 :=
  if h : s.Prime then
    letI : NeZero s := ⟨h.ne_zero⟩
    aksBranch n s
  else constant false

def primalityNet (n : ℕ) : BooleanNetwork (rootWidth n) 1 :=
  (perfectPowerNet n).bnot.band
    (any (List.ofFn (fun s : Fin (n^8+1) => aksStaticBranch n s.val)))

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_BoundedStack
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


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

/-- A fixed-capacity little-endian word stack. No dynamic address or unbounded
list is part of the corresponding Boolean network. -/
def stackEncoding (s w : ℕ) (xs : List (Basis w)) : Basis (s*w) := fun j =>
  let ij := finProdFinEquiv.symm j
  (xs[ij.1.val]?.getD (fun _ => false)) ij.2

/-- Pop the top, padding the empty end with zero. -/
def stackPop (s w : ℕ) : BooleanNetwork (s*w) (s*w) :=
  wordBlocks (fun i : Fin s => if h : i.val+1 < s then blockNet s w ⟨i.val+1,h⟩
    else wordConstant 0)

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactorVerifier
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork
open scoped BigOperators

/-- The range check makes the AKS interface exact also for the invalid 0,1
entries occurring in arbitrary uniform guesses. -/
def primeWord (n : ℕ) : BooleanNetwork n 1 :=
  (wordLe (wordConstant (BitVec.ofNat n 2)) (select id)).band
    ((resizeWord n (rootWidth n)).comp (primalityNet n))

def zeroWord {k n : ℕ} (a : BooleanNetwork k n) : BooleanNetwork k 1 :=
  equalOn a (wordConstant 0)

def primeOrZero {k n : ℕ} (a : BooleanNetwork k n) : BooleanNetwork k 1 :=
  (zeroWord a).bor (a.comp (primeWord n))

def paddedPair {k n : ℕ} (a b : BooleanNetwork k n) : BooleanNetwork k 1 :=
  (zeroWord b).bor ((zeroWord a).bnot.band (wordLe a b))

def unpadWord {k n : ℕ} (a : BooleanNetwork k n) : BooleanNetwork k n :=
  wordMux (zeroWord a) (wordConstant 1) a

/-- Multiplication is modulo the sufficiently wide product register; no
repetition of earlier expression DAGs occurs in this linear fold. -/
def productNet {k w : ℕ} : List (BooleanNetwork k w) → BooleanNetwork k w
  | [] => wordConstant 1
  | a::as => (a.pair (productNet as)).comp (mul w)

def candidateWords {k n : ℕ} (as : Fin n→BooleanNetwork k n) (x : Basis k) : List ℕ :=
  List.ofFn (fun i => (bitsValue ((as i).eval x)).toNat)

def candidateProduct {k n : ℕ} (as : Fin n→BooleanNetwork k n) : BooleanNetwork k (rootWidth n) :=
  productNet (List.ofFn (fun i => (unpadWord (as i)).comp (resizeWord n (rootWidth n))))

def factorVerifierOn {k n : ℕ} (N : BooleanNetwork k n) (as : Fin n→BooleanNetwork k n) :
    BooleanNetwork k 1 :=
  ((all (List.ofFn (fun i => primeOrZero (as i)))).band
    (all (List.ofFn (fun i : Fin (n*n) =>
      let p := finProdFinEquiv.symm i
      if p.1<p.2 then paddedPair (as p.1) (as p.2) else constant true)))).band
    (equalOn (candidateProduct as) (N.comp (resizeWord n (rootWidth n))))

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

def primeComponent {k n : ℕ} (m p : BooleanNetwork k n) : BooleanNetwork k n :=
  let w:=componentWidth n
  let mw:=m.comp (resizeWord n w)
  let pw:=p.comp (resizeWord n w)
  ((mw.pair (productNet (List.replicate n pw))).comp (gcdNet w)).comp (resizeWord w n)

end BitArithmetic
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

namespace BitArithmetic

def powOn {k w : ℕ} (a m e : BooleanNetwork k w) : BooleanNetwork k w :=
  ((a.pair m).pair (e.rewire Fin.rev)).comp (modularPower w w)

def stripOn {k w : ℕ} (a m q v : BooleanNetwork k w) : BooleanNetwork k w :=
  let d := (v.pair q).comp (div w)
  let cond := (equalOn ((v.pair q).comp (mod w)) (wordConstant (BitVec.ofNat w 0))).band
    (equalOn (powOn a m d) (wordConstant (BitVec.ofNat w 1)))
  wordMux cond d v

/-- The original input stays read-only; the accumulator is updated once. -/
def stripUpdate {k w : ℕ} (a m q : BooleanNetwork k w) : BooleanNetwork (k+w) (k+w) :=
  (select (Fin.castAdd w)).pair (stripOn (liftInput a (Fin.castAdd w))
    (liftInput m (Fin.castAdd w)) (liftInput q (Fin.castAdd w)) (select (Fin.natAdd k)))

def stripScan {k w : ℕ} (a m : BooleanNetwork k w) : List (BooleanNetwork k w)→BooleanNetwork (k+w) (k+w)
  | [] => select id
  | q::qs => (stripUpdate a m q).comp (stripScan a m qs)

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactorGuess
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BitArithmetic BooleanNetwork Exactness

/-- The specified sorted, zero-padded n²-bit root encoding. -/
def guessWords (n : ℕ) (x : Basis (n*n)) : List ℕ :=
  List.ofFn (fun i : Fin n => (bitsValue (block x i)).toNat)

noncomputable def fairState (b : ℕ) : State b := fun _ => (Real.sqrt 2:ℂ)⁻¹^b

/-- Concrete Boolean root-verification circuit with no run-time primality or
factorization oracle. The integer input is retained separately from the guess. -/
def guessVerifier (n : ℕ) : BooleanNetwork (n+n*n) 1 :=
  factorVerifierOn (select (Fin.castAdd (n*n)))
    (fun i => select (fun j => Fin.natAdd n (finProdFinEquiv (i,j))))

end ExactQuantumFactoring


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

def forward {p b : ℕ} (δ : BooleanNetwork p b) : BooleanNetwork (p+b) (p+b) :=
  (select (fun i => i.castAdd b)).pair ((addInput δ).comp (BitArithmetic.add b))

def backward {p b : ℕ} (δ : BooleanNetwork p b) : BooleanNetwork (p+b) (p+b) :=
  (select (fun i => i.castAdd b)).pair ((addInput δ).comp (BitArithmetic.sub b))

lemma forward_count {p b : ℕ} (δ : BooleanNetwork p b) :
    (forward δ).net.count ≤ δ.net.count+86*b+6 := by
  simp only [forward, addInput, count_pair, count_comp, count_select, Nat.zero_add]
  have := BitArithmetic.add_count b
  omega

lemma backward_count {p b : ℕ} (δ : BooleanNetwork p b) :
    (backward δ).net.count ≤ δ.net.count+158*b+6 := by
  simp only [backward, addInput, count_pair, count_comp, count_select, Nat.zero_add]
  have := BitArithmetic.sub_count b
  omega

end ControlledTranslation
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TriangularCircuit
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.blockNet_count _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

lemma translation_count_forward {b : ℕ} (j : Fin b) :
    (ControlledTranslation.forward (rowNetwork j)).net.count ≤ work b := by
  have h := ControlledTranslation.forward_count (rowNetwork j)
  rw [rowNetwork_count] at h
  dsimp [work]
  omega

lemma translation_count_backward {b : ℕ} (j : Fin b) :
    (ControlledTranslation.backward (rowNetwork j)).net.count ≤ work b := by
  have h := ControlledTranslation.backward_count (rowNetwork j)
  rw [rowNetwork_count] at h
  dsimp [work]
  omega

def translation {b : ℕ} (j : Fin b) : List (Instruction (width b)) :=
  cleanPermutation (ControlledTranslation.forward (rowNetwork j))
    (ControlledTranslation.backward (rowNetwork j))
    (translation_count_forward j) (translation_count_backward j)

def rowCircuit {b : ℕ} (j : Fin b) : List (Instruction (width b)) :=
  [hadamardAt (dataWire j)] ++ translation j

def triPrefix (b : ℕ) : (k : ℕ) → k ≤ b → List (Instruction (width b))
  | 0, _ => []
  | k+1, h => triPrefix b k (by omega) ++ rowCircuit ⟨k,by omega⟩

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

/-- Preparation, actual clean triangular gate program, inverse preparation.
The success event is the all-zero phase and scratch register; it is not enforced. -/
def transform (a : ℕ) : List (Instruction (width (a+2))) :=
  preparation a ++ triPrefix (a+2) (a+2) le_rfl ++
    (preparation a).reverse.map Instruction.reverse

end ExactQuantumFactoring.Triangular


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderSampleCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
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

noncomputable def inputWord {w b : ℕ} (a m : Basis w) (x : Basis b) :
    Basis (inputWidth w b) := Fin.append (Fin.append a m) (Triangular.encode b (x,0))

def powerNetwork (w b : ℕ) : BooleanNetwork (inputWidth w b) w :=
  (powerInputs w b).comp (BitArithmetic.modularPower w b)

lemma powerNetwork_count (w b : ℕ) : (powerNetwork w b).net.count ≤
    w+b*(3672*w*w+436*w+36) := by
  simpa only [powerNetwork,count_comp,powerInputs,count_select,zero_add] using
    BitArithmetic.modularPower_count w b

def program (w s : ℕ) : List (Instruction (width w (s+2))) :=
  sampleProgram (powerNetwork w (s+2)) (powerNetwork_count w (s+2))
    (rightProgram (w+w) (Triangular.transform s))

noncomputable def word {w b : ℕ} (a m : Basis w) (x : Basis b) (u : Basis w) :
    Basis (width w b) := packed (scratch w b) (inputWord a m x) u

noncomputable def uniformInput (w b : ℕ) (a m : Basis w) : State (width w b) :=
  encodeState (fun x : Basis b => word a m x (fun _ => false))
    (fun _ => (Real.sqrt ((2:ℝ)^b):ℂ)⁻¹)

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

namespace OrderSample

def completeSampler (w s : ℕ) : List (Instruction (width w (s+2))) :=
  initial w (s+2) ++ program w s

end OrderSample
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderSamplerMass
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
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

/-- Exact bit representation used for modular-power values. -/
def natBasis (w z : ℕ) : Basis w := fun i => (BitVec.ofNat w z).getLsbD i.val

/-- Embed all units into the physical modular-power register, when m<2^w. -/
def unitWord {m w : ℕ} (u : (ZMod m)ˣ) : Basis w := natBasis w (u : ZMod m).val

noncomputable def samplerState {w s : ℕ} (a m : Basis w) : State (OrderSample.width w (s+2)) :=
  (programMatrix (OrderSample.completeSampler w s)).mulVec
    (basisVector (OrderSample.word a m (fun _=>false) (fun _=>false)))

end OrderTrial
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ParallelPreparation
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
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

def appendEquiv (p q : ℕ) : Basis p × Basis q ≃ Basis (p+q) :=
  Fin.appendEquiv p q

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ThresholdRetention
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
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

def bitsNatEquiv (b : ℕ) : Basis b ≃ Fin (2^b) :=
  (bitsEquiv b).trans BitVec.equivFin.toEquiv

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TrialGuessLaw
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
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
open Exactness

abbrev Guesses (n : ℕ) := Basis n × (Basis n × (Basis n × Basis (retentionBits n)))

noncomputable def guessState (n : ℕ) : Guesses n→ℂ :=
  independentState (fairState n) (independentState (fairState n)
    (independentState (fairState n) (fairState (retentionBits n))))

def Retains {n : ℕ} (p : ℚ) (c : Basis (retentionBits n)) : Prop :=
  (bitsValue c).toNat<(Int.floor (p*(2:ℚ)^(retentionBits n))).toNat

noncomputable def firstPass (n d j : ℕ) (x : Guesses n) : Prop :=
  Retains (firstRetention n d j) x.2.2.2
noncomputable def secondPass (n d j : ℕ) (x : Guesses n) : Prop :=
  (bitsValue x.1).toNat=d ∧ (bitsValue x.2.1).toNat=j ∧
    (bitsValue x.2.2.1).toNat<d ∧
      Retains (discrepancyRetention n d j (bitsValue x.2.2.1).toNat) x.2.2.2
noncomputable def thirdPass (n d j : ℕ) (x : Guesses n) : Prop :=
  (bitsValue x.1).toNat=d ∧ (bitsValue x.2.1).toNat=j ∧
    Retains (remainderRetention n d j) x.2.2.2

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TrialRawPreparation
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
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

def productLayout {α β : Type*} {p q : ℕ} (e : α≃Basis p) (f : β≃Basis q) :
    α×β≃Basis (p+q) := (Equiv.prodCongr e f).trans (appendEquiv p q)

namespace OrderTrial

def guessLayout (n : ℕ) : Guesses n≃Basis (guessWidth n) :=
  productLayout (Equiv.refl _) (productLayout (Equiv.refl _)
    (productLayout (Equiv.refl _) (Equiv.refl _)))
def guessZero (n : ℕ) : Guesses n := ((fun _ => false),(fun _ => false),(fun _ => false),(fun _ => false))

abbrev Raw (w s n : ℕ) := Basis 2 × (Basis (OrderSample.width w (s+2)) × Guesses n)
def rawLayout (w s n : ℕ) : Raw w s n≃Basis (rawWidth w s n) :=
  productLayout (Equiv.refl _) (productLayout (Equiv.refl _) (guessLayout n))
def rawProgram (w s n : ℕ) : List (Instruction (rawWidth w s n)) :=
  parallelProgram (hadamardPrefix 2 2 le_rfl)
    (parallelProgram (OrderSample.completeSampler w s) (guessProgram n))
noncomputable def rawZero {w : ℕ} (s n : ℕ) (a m : Basis w) : Raw w s n :=
  ((fun _ => false),OrderSample.word a m (fun _ => false) (fun _ => false),guessZero n)
noncomputable def rawState {w : ℕ} (s n : ℕ) (a m : Basis w) : Raw w s n→ℂ :=
  independentState (fairState 2) (independentState (samplerState (s:=s) a m) (guessState n))

end OrderTrial
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_DyadicCompletion
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
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

abbrev Raw (α : Type*) (W t d : ℕ) := Basis t × (α × (Basis W × Basis (coinBits W t d)))
noncomputable def fresh {α : Type*} (ψ : α→ℂ) (W t d : ℕ) : Raw α W t d→ℂ :=
  independentState (fairState t) (independentState ψ
    (independentState (fairState W) (fairState (coinBits W t d))))

def rare {t : ℕ} (b : Basis t) : Prop := (bitsValue b).toNat=0
instance instDecidableRare {t : ℕ} (b : Basis t) : Decidable (rare b) :=
  inferInstanceAs (Decidable ((bitsValue b).toNat=0))

def threshold {D : ℕ} (p : ℚ) (b : Basis D) : Prop :=
  (bitsValue b).toNat<(Int.floor (p*(2:ℚ)^D)).toNat

def output {α : Type*} {W t d : ℕ} (ordinary : α→Basis W) (r : Raw α W t d) : Basis W :=
  if rare r.1 then r.2.2.1 else ordinary r.2.1

def ordinaryPass {α : Type*} {W t d : ℕ} (good : α→Prop) (s z : ℚ) (r : Raw α W t d) : Prop :=
  ¬rare r.1 ∧ (good r.2.1 ∧ threshold (coeff W t s z) r.2.2.2)
def guessPass {α : Type*} {W t d : ℕ} (y₀ : Basis W) (s z : ℚ) (r : Raw α W t d) : Prop :=
  rare r.1 ∧ (r.2.2.1=y₀ ∧ threshold (guessRetention W t s z) r.2.2.2)
def passed {α : Type*} {W t d : ℕ} (good : α→Prop) (y₀ : Basis W) (s z : ℚ) (r : Raw α W t d) : Prop :=
  ordinaryPass good s z r ∨ guessPass y₀ s z r

def layout (q W t d : ℕ) : Raw (Basis q) W t d ≃ Basis (t+(q+(W+coinBits W t d))) :=
  productLayout (Equiv.refl _) (productLayout (Equiv.refl _) (productLayout (Equiv.refl _) (Equiv.refl _)))

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

/-- Choose the left nonzero-denominator pair, otherwise the right. The costly
candidate and recursive scan are paired ONCE before this inexpensive mux. -/
def pairChoice (w : ℕ) : BooleanNetwork ((w+w)+(w+w)) (w+w) :=
  let left := rootModulus (w+w)
  let right := rootGuess (w+w)
  let den := left.comp (rootModulus w)
  let zero := equalOn den (wordConstant (BitVec.ofNat w 0))
  wordMux zero right left

def recoveryNet {n w : ℕ} (Q B k : BooleanNetwork n w) : ℕ → BooleanNetwork n (w+w)
  | 0 => (wordConstant (BitVec.ofNat w 0)).pair (wordConstant (BitVec.ofNat w 0))
  | i+1 => ((checkedConvergent i Q B k).pair (recoveryNet Q B k i)).comp (pairChoice w)

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SamplerLabels
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork

def sampleY {w b : ℕ} (x : Basis (OrderSample.width w b)) : Basis b :=
  fun i => x (((Fin.natAdd (w+w) (Triangular.dataWire i)).castAdd w).castAdd (OrderSample.scratch w b))
def sampleU {w b : ℕ} (x : Basis (OrderSample.width w b)) : Basis w :=
  fun i => x ((Fin.natAdd (OrderSample.inputWidth w b) i).castAdd (OrderSample.scratch w b))

/-- Selected phase block, with every workspace bit accounted for. The input
copies are compared to their retained read-only values. -/
def SampleSelected {w b : ℕ} (a m : Basis w) (x : Basis (OrderSample.width w b)) : Prop :=
  x=OrderSample.word a m (sampleY x) (sampleU x)

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalTrialLaw
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
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
open Exactness

noncomputable def recovered {w s : ℕ} (a m : Basis w) (n d j : ℕ)
    (x : Basis (OrderSample.width w (s+2))) : Prop :=
  SampleSelected a m x ∧
    scanPairs (2^(s+2)) (2^n) (Triangular.outputNumber (sampleY x)) (2*(s+3)+1)=(d,j)

noncomputable def modeFirst {w : ℕ} (s n : ℕ) (a m : Basis w) (d j : ℕ) (x : Raw w s n) : Prop :=
  (bitsValue x.1).toNat<2 ∧ recovered a m n d j x.2.1 ∧ firstPass n d j x.2.2
noncomputable def modeSecond {w : ℕ} (s n d j : ℕ) (x : Raw w s n) : Prop :=
  (bitsValue x.1).toNat=2 ∧ secondPass n d j x.2.2
noncomputable def modeThird {w : ℕ} (s n d j : ℕ) (x : Raw w s n) : Prop :=
  (bitsValue x.1).toNat=3 ∧ thirdPass n d j x.2.2

noncomputable def labelEvent {w : ℕ} (s n : ℕ) (a m : Basis w) (d j : ℕ) (x : Raw w s n) : Prop :=
  modeFirst s n a m d j x ∨ modeSecond s n d j x ∨ modeThird s n d j x

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderCandidateLaw
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
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

noncomputable def labelPair {w : ℕ} (s n : ℕ) (x : Raw w s n) : ℕ×ℕ :=
  if (bitsValue x.1).toNat<2 then
    scanPairs (2^(s+2)) (2^n) (Triangular.outputNumber (sampleY x.2.1)) (2*(s+3)+1)
  else ((bitsValue x.2.2.1).toNat,(bitsValue x.2.2.2.1).toNat)

/-- Arithmetic validation is performed in every mode, before any returned
candidate is used. The plain scan/guess never serves as an order certificate. -/
noncomputable def trialResult {w : ℕ} (s n : ℕ) (a m : Basis w) (x : Raw w s n) : Option ℕ := by
  classical
  let dj := labelPair s n x
  exact if ValidLabel n (bitsValue a).toNat (bitsValue m).toNat dj.1 dj.2 ∧
      labelEvent s n a m dj.1 dj.2 x then some dj.1 else none

end OrderTrial
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ListTransition
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
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


/-! The actual uniform-list transition in Section 5: its event, exact closed
probability, and unchanged repetition guarantee. -/
namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials

noncomputable def FavorableBits {m n : ℕ} (hm : m ≠ 0) (hb : m < 2^n)
    (p₀ : Component m) (b : ℕ) (x : Basis b) : Prop :=
  ∃ a : (ZMod m)ˣ, (a : ZMod m).val=(bitsValue x).toNat ∧ FavorableUnit hm hb p₀ a

noncomputable def GoodList {m n : ℕ} (hm : m ≠ 0) (hb : m < 2^n)
    (p₀ : Component m) (K : ℕ) (x : Fin K→Basis (Nat.clog 2 m)) : Prop :=
  ∃ i, FavorableBits hm hb p₀ (Nat.clog 2 m) (x i)

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_OrderTransition
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
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

/-- The source order transition ignores empty trials and returns the least
nonempty candidate, with zero for the entirely empty list. -/
noncomputable def orderResult {w : ℕ} (s n : ℕ) (a m : Basis w) (K : ℕ)
    (x : Fin K→Raw w s n) : ℕ :=
  (minimumCandidate (List.ofFn (fun i => trialResult s n a m (x i)))).getD 0

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CompletedOrderSlots
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
open Exactness RepeatedTrials OrderTrial

namespace OrderSlots

abbrev Result (n : ℕ) := Completion.Raw (Fin (n^5)→OrderTrial.Raw n (sampleExponent n) n)
  (Completion.transitionWidth n) (2*n) ((n+10)*n^5)

noncomputable instance resultFintype (n : ℕ) : Fintype (Result n) := inferInstance

noncomputable def fresh (n : ℕ) (a m : Basis n) : Result n→ℂ :=
  Completion.fresh (tensorState (rawState (sampleExponent n) n a m) (n^5))
    (Completion.transitionWidth n) (2*n) ((n+10)*n^5)

def Usable {n : ℕ} (a m : Basis n) : Prop :=
  (bitsValue a).toNat < (bitsValue m).toNat ∧
    IsUnit ((bitsValue a).toNat : ZMod (bitsValue m).toNat)

noncomputable def unitOrder {n : ℕ} (a m : Basis n) : ℕ := by
  classical
  exact if h : Usable a m then orderOf h.2.unit else 0

noncomputable def canonical {n : ℕ} (a m : Basis n) : Basis (Completion.transitionWidth n) :=
  natBasis _ (unitOrder a m)

noncomputable def ordinary {n : ℕ} (a m : Basis n)
    (r : Fin (n^5)→OrderTrial.Raw n (sampleExponent n) n) : Basis (Completion.transitionWidth n) := by
  classical
  exact if Usable a m then
    natBasis _ (orderResult (sampleExponent n) n a m (n^5) r) else natBasis _ 0

noncomputable def passed {n : ℕ} (a m : Basis n) : Result n→Prop := by
  classical
  exact if h : Usable a m then
    Completion.passed (fun r => orderResult (sampleExponent n) n a m (n^5) r=orderOf h.2.unit)
      (canonical a m) (Completion.orderSuccess (orderOf h.2.unit) (n^5)) (Completion.target n)
  else Completion.passed (fun _ => True) (canonical a m) 1 (Completion.target n)

noncomputable def output {n : ℕ} (a m : Basis n) : Result n→Basis (Completion.transitionWidth n) :=
  Completion.output (ordinary a m)

end OrderSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CanonicalTransition
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
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

noncomputable def canonicalList {m : ℕ} (hm : m≠0) (p₀ : Component m) (K : ℕ) :
    Fin K→Basis (Nat.clog 2 m) := fun i =>
  (bitsEquiv _).symm (BitVec.ofNat (Nat.clog 2 m) (if i.val=0 then (canonicalUnit hm p₀ : ZMod m).val else 0))

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RuntimeListPreparation
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
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

/-- Compute ceil-log activation bits by bounded comparisons. The constant
2^i fits n bits, and the circuit is polynomial on invalid inputs too. -/
def listMaskNet (n : ℕ) : BooleanNetwork n n :=
  vector (fun i : Fin n => wordLt (wordConstant (BitVec.ofNat n (2^i.val))) (select id))

lemma listMaskNet_count (n : ℕ) : (listMaskNet n).net.count ≤ n*(49*n+8) := by
  apply count_vector_le
  intro i
  have hh := wordLt_count (wordConstant (n:=n) (BitVec.ofNat n (2^i.val))) (select id)
  simp only [wordConstant_count,count_select,add_zero] at hh
  omega

def padBits {b n : ℕ} (_h : b ≤ n) (x : Basis b) : Basis n :=
  fun i => if hi : i.val<b then x ⟨i.val,hi⟩ else false

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TransitionWords
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
open Exactness RepeatedTrials

namespace TransitionWords

/-- K n-bit words in consecutive little-endian fields, followed by one zero
word. This fits exactly the source's W=n(K+1) output cap. -/
def encode {n K : ℕ} (a : Fin K→Basis n) : Basis (n*(K+1)) := fun i =>
  let j := finProdFinEquiv.symm (Fin.cast (Nat.mul_comm _ _) i)
  if h : j.1.val<K then a ⟨j.1.val,h⟩ j.2 else false

def read {n K : ℕ} (x : Basis (n*(K+1))) (i : Fin K) : Basis n := fun j =>
  x (Fin.cast (Nat.mul_comm _ _) (finProdFinEquiv (i.castSucc,j)))

end TransitionWords

namespace ListSlots

abbrev Ordinary (n m : ℕ) := Fin (K n)→Basis (Nat.clog 2 m)

def ordinary {n m : ℕ} (hb : m < 2^n) (x : Ordinary n m) : Basis (Completion.transitionWidth n) :=
  TransitionWords.encode (fun i => padBits (Nat.clog_le_of_le_pow hb.le) (x i))

noncomputable def canonical {n m : ℕ} (hm : m ≠ 0) (hb : m < 2^n) (p₀ : Component m) :
    Basis (Completion.transitionWidth n) := ordinary hb (canonicalList hm p₀ (K n))

noncomputable def GoodOutput {n m : ℕ} (hm : m ≠ 0) (hb : m < 2^n) (p₀ : Component m)
    (y : Basis (Completion.transitionWidth n)) : Prop :=
  ∃ (i : Fin (K n)) (u : (ZMod m)ˣ),
    (bitsValue (TransitionWords.read y i)).toNat=(u : ZMod m).val ∧ FavorableUnit hm hb p₀ u

end ListSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ListSamplerCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
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

def word {n : ℕ} (m mask y : Basis n) : Basis (width n) := fun i =>
  if h₀ : i.val<n then m ⟨i.val,h₀⟩ else
  if h₁ : i.val<n+n then mask ⟨i.val-n,by omega⟩ else
  if h₂ : i.val<n+n+n then y ⟨i.val-(n+n),by omega⟩ else false

/-- A single family (depending only on n) prepares the manuscript's exact
runtime-b(n,m) fair sample. No Hadamard is chosen by a metalevel value of m. -/
def circuit (n : ℕ) : List (Instruction (width n)) :=
  oracleOn (listMaskNet n) (show (listMaskNet n).net.count ≤ n+work n from
    (listMaskNet_count n).trans (Nat.le_add_left _ _)) ++
  (maskedPrefix n n le_rfl).map (Instruction.place (maskRegister n))

end ExactQuantumFactoring.ListSampler


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TensorPreparation
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
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

def tensorLayout (q : ℕ) : (K : ℕ)→(Fin K→Basis q)≃Basis (tensorWidth q K)
  | 0 => Equiv.ofUnique _ _
  | K+1 => (Fin.consEquiv (fun _ : Fin (K+1) => Basis q)).symm.trans
      (productLayout (Equiv.refl _) (tensorLayout q K))

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalListSlots
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.OrderSlots.resultFintype
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

abbrev Result (n : ℕ) := Completion.Raw (Basis (ordinaryWidth n))
  (Completion.transitionWidth n) (2*n) (n*n^5)
noncomputable instance resultFintype (n : ℕ) : Fintype (Result n) := inferInstance

def sampleRead {n : ℕ} (x : Basis (ListSampler.width n)) : Basis n := fun i =>
  x ⟨n+n+i.val,by have := i.isLt; dsimp [ListSampler.width]; omega⟩

def ordinary {n : ℕ} (x : Basis (ordinaryWidth n)) : Basis (Completion.transitionWidth n) :=
  TransitionWords.encode (fun i => sampleRead ((tensorLayout _ (n^5)).symm x i))

def ordinaryProgram (n : ℕ) : List (Instruction (ordinaryWidth n)) :=
  tensorProgram (ListSampler.circuit n) (n^5)

def ordinaryZero {n : ℕ} (m : Basis n) : Basis (ordinaryWidth n) :=
  tensorLayout _ (n^5) (fun _ => ListSampler.word m (fun _ => false) (fun _ => false))

noncomputable def ordinaryState {n : ℕ} (m : Basis n) : State (ordinaryWidth n) :=
  (programMatrix (ordinaryProgram n)).mulVec (basisVector (ordinaryZero m))

noncomputable def fresh {n : ℕ} (m : Basis n) : Result n→ℂ :=
  Completion.fresh (ordinaryState m) (Completion.transitionWidth n) (2*n) (n*n^5)
noncomputable def passed {n : ℕ} (m : Basis n) (hm : (bitsValue m).toNat≠0)
    (p₀ : Component (bitsValue m).toNat) : Result n→Prop :=
  Completion.passed (ListSlots.GoodOutput hm (bitsValue m).isLt p₀ ∘ ordinary)
    (ListSlots.canonical hm (bitsValue m).isLt p₀)
    (Completion.listSuccess (bitsValue m).toNat n (n^5)) (Completion.target n)
def output {n : ℕ} : Result n→Basis (Completion.transitionWidth n) := Completion.output ordinary

def layout (n : ℕ) : Result n≃Basis (width n) := Completion.layout _ _ _ _
def program (n : ℕ) : List (Instruction (width n)) :=
  Completion.program (ordinaryProgram n) (Completion.transitionWidth n) (2*n) (n*n^5)
def zero {n : ℕ} (m : Basis n) : Result n :=
  ((fun _ => false),ordinaryZero m,(fun _ => false),(fun _ => false))

end PhysicalListSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FixedSplit
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
open Exactness RepeatedTrials OrderTrial

namespace FixedSplit

abbrev Raw (n : ℕ) :=
  PhysicalListSlots.Result n × (Fin (n^5)→OrderSlots.Result n)

noncomputable instance rawFintype (n : ℕ) : Fintype (Raw n) := inferInstance

def bases {n : ℕ} (r : PhysicalListSlots.Result n) : Fin (n^5)→Basis n :=
  TransitionWords.read (PhysicalListSlots.output r)

/-- Actual next fresh registers depend only on the completed list output,
including its rare guessing branch. Previous outcomes remain in the record. -/
noncomputable def fresh {n : ℕ} (m : Basis n) : Raw n→ℂ :=
  RecordedHistory.appendState (PhysicalListSlots.fresh m)
    (fun l => productState (fun i => OrderSlots.fresh n (bases l i) m))

noncomputable def passed {n : ℕ} (m : Basis n) (hm : (bitsValue m).toNat≠0)
    (p₀ : Component (bitsValue m).toNat) (r : Raw n) : Prop :=
  PhysicalListSlots.passed m hm p₀ r.1 ∧
    ∀ i,OrderSlots.passed (bases r.1 i) m (r.2 i)

noncomputable def pairs {n : ℕ} (m : Basis n) (r : Raw n) : List (ℕ×ℕ) :=
  List.ofFn (fun i : Fin (n^5) => ((bitsValue (bases r.1 i)).toNat,
    (bitsValue (OrderSlots.output (bases r.1 i) m (r.2 i))).toNat))

noncomputable def divisor {n : ℕ} (m : Basis n) (r : Raw n) : ℕ :=
  suppliedDivisor (bitsValue m).toNat n (pairs m r)

end FixedSplit
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_UniversalSplit
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
open Exactness RepeatedTrials OrderTrial
namespace UniversalSplit

/-- The unchanging request register dimensions depend only on the original n. -/
abbrev Raw := FixedSplit.Raw

noncomputable def dummyList {n : ℕ} : PhysicalListSlots.Result n→Prop :=
  Completion.passed (fun _=>True) (natBasis _ 0) 1 (Completion.target n)
noncomputable def dummyOrder {n : ℕ} : OrderSlots.Result n→Prop :=
  Completion.passed (fun _=>True) (natBasis _ 0) 1 (Completion.target n)
noncomputable def dummy {n : ℕ} (r : Raw n) : Prop := dummyList r.1 ∧ ∀ i,dummyOrder (r.2 i)

noncomputable def passed {n : ℕ} (m : Basis n) : Raw n→Prop := by
  classical
  exact if h : Hard (bitsValue m).toNat then
    FixedSplit.passed m (by have := h.1; omega) (firstComponent h.1) else dummy

end UniversalSplit
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

def rareWires (q W t d : ℕ) : BooleanNetwork (totalWidth q W t d) t :=
  select (Fin.castAdd (q+(W+coinBits W t d)))
def ordinaryWires (q W t d : ℕ) : BooleanNetwork (totalWidth q W t d) q :=
  select (fun i => Fin.natAdd t (i.castAdd (W+coinBits W t d)))
def guessWires (q W t d : ℕ) : BooleanNetwork (totalWidth q W t d) W :=
  select (fun i => Fin.natAdd t (Fin.natAdd q (i.castAdd (coinBits W t d))))
def retentionWires (q W t d : ℕ) : BooleanNetwork (totalWidth q W t d) (coinBits W t d) :=
  select (fun i => Fin.natAdd t (Fin.natAdd q (Fin.natAdd W i)))

def rareNet (q W t d : ℕ) : BooleanNetwork (totalWidth q W t d) 1 :=
  equalOn (rareWires q W t d) (wordConstant (BitVec.ofNat t 0))

/-- Runtime output selection retains the entire unused ordinary computation even
on the rare branch. Neither success statistics nor future auxiliary data enter
this network. -/
def outputNet {q W : ℕ} (ordinary : BooleanNetwork q W) (t d : ℕ) :
    BooleanNetwork (totalWidth q W t d) W :=
  wordMux (rareNet q W t d) (guessWires q W t d)
    ((ordinaryWires q W t d).comp ordinary)

/-- Constant-zero fresh blocks are explicit gates, rather than analytical
initialization assumptions about the raw sampler layout. -/
def zeros (k m : ℕ) : BooleanNetwork k m := vector (fun _ => constant false)

def initialNet {k q : ℕ} (ordinary : BooleanNetwork k q) (W t d : ℕ) :
    BooleanNetwork k (totalWidth q W t d) :=
  (zeros k t).pair (ordinary.pair ((zeros k W).pair (zeros k (coinBits W t d))))

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

def tensorSelect (q K : ℕ) (i : Fin K) : BooleanNetwork (tensorWidth q K) q :=
  select (tensorWire q K i)

/-- Direct concatenation prepares K fixed blocks. No branch-indexed truth table
is allocated; the count is the sum of the supplied K finite networks. -/
def tensorNetwork {n q : ℕ} : {K : ℕ} → (Fin K → BooleanNetwork n q) →
    BooleanNetwork n (tensorWidth q K)
  | 0,_ => select Fin.elim0
  | _K+1,f => (f 0).pair (tensorNetwork (fun i => f i.succ))

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TransitionNetworks
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
namespace TransitionWords

/-- Each field is wired into its fixed source layout, and the final unused word
is explicitly zeroed. The cap K and all placements are independent of inputs. -/
def encodeNet {k n K : ℕ} (f : Fin K → BooleanNetwork k n) : BooleanNetwork k (n*(K+1)) :=
  vector (fun i =>
    let j := finProdFinEquiv.symm (Fin.cast (Nat.mul_comm _ _) i)
    if h : j.1.val<K then (f ⟨j.1.val,h⟩).rewire (fun _ => j.2) else constant false)

end TransitionWords
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalListNetworks
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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
namespace PhysicalListSlots

def sampleNet (n : ℕ) : BooleanNetwork (ListSampler.width n) n :=
  select (fun i => ⟨n+n+i.val,by have := i.isLt; dsimp [ListSampler.width]; omega⟩)

def ordinaryNet (n : ℕ) : BooleanNetwork (ordinaryWidth n) (Completion.transitionWidth n) :=
  TransitionWords.encodeNet (fun i : Fin (n^5) => (tensorSelect (ListSampler.width n) (n^5) i).comp (sampleNet n))

def outputNet (n : ℕ) : BooleanNetwork (width n) (Completion.transitionWidth n) :=
  Completion.outputNet (ordinaryNet n) (2*n) (n*n^5)

/-- Copy the runtime modulus into each literal sampler block; all other input
cells are zero. Only fixed wire placements and constants are used. -/
def singleZeroNet (n : ℕ) : BooleanNetwork n (ListSampler.width n) :=
  vector (fun i => if h : i.val<n then bit ⟨i.val,h⟩ else constant false)

def ordinaryZeroNet (n : ℕ) : BooleanNetwork n (ordinaryWidth n) :=
  tensorNetwork (fun _ : Fin (n^5) => singleZeroNet n)

def initialNet (n : ℕ) : BooleanNetwork n (width n) :=
  Completion.initialNet (ordinaryZeroNet n) (Completion.transitionWidth n) (2*n) (n*n^5)

abbrev work (n : ℕ) := (initialNet n).net.count
abbrev launchWidth (n : ℕ) := n+width n+work n
/-- Length-uniform placement of the completed runtime-modulus list sampler. -/
def launch (n : ℕ) : List (Instruction (launchWidth n)) :=
  preparedOracle (initialNet n) le_rfl (program n)

end PhysicalListSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalOrderSlots
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
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

def ordinaryLayout (n : ℕ) : (Fin (n^5)→OrderTrial.Raw n (sampleExponent n) n)≃Basis (ordinaryWidth n) :=
  (Equiv.piCongrRight (fun _ => rawLayout n (sampleExponent n) n)).trans
    (tensorLayout (rawWidth n (sampleExponent n) n) (n^5))
def layout (n : ℕ) : Result n≃Basis (width n) :=
  productLayout (Equiv.refl _) (productLayout (ordinaryLayout n)
    (productLayout (Equiv.refl _) (Equiv.refl _)))

def program (n : ℕ) : List (Instruction (width n)) :=
  Completion.program (tensorProgram (rawProgram n (sampleExponent n) n) (n^5))
    (Completion.transitionWidth n) (2*n) ((n+10)*n^5)

noncomputable def zero {n : ℕ} (a m : Basis n) : Result n :=
  ((fun _ => false),(fun _ => rawZero (sampleExponent n) n a m),(fun _ => false),(fun _ => false))

end OrderSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalOrderNetworks
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

namespace BooleanNetwork

def packNet {k n m : ℕ} (r : ℕ) (a : BooleanNetwork k n) (b : BooleanNetwork k m) :
    BooleanNetwork k (n+m+r) := (a.pair b).pair (Completion.zeros k r)

end BooleanNetwork

namespace OrderSlots

def samplerZeroNet (w b : ℕ) : BooleanNetwork (w+w) (OrderSample.width w b) :=
  packNet (OrderSample.scratch w b)
    ((select id).pair (Completion.zeros (w+w) (Triangular.width b))) (Completion.zeros (w+w) w)

def rawZeroNet (n : ℕ) : BooleanNetwork (n+n) (OrderTrial.rawWidth n (sampleExponent n) n) :=
  (Completion.zeros (n+n) 2).pair
    ((samplerZeroNet n (sampleExponent n+2)).pair (Completion.zeros (n+n) (OrderTrial.guessWidth n)))

def ordinaryZeroNet (n : ℕ) : BooleanNetwork (n+n) (ordinaryWidth n) :=
  tensorNetwork (fun _ : Fin (n^5)=>rawZeroNet n)

def initialNet (n : ℕ) : BooleanNetwork (n+n) (width n) :=
  Completion.initialNet (ordinaryZeroNet n) (Completion.transitionWidth n) (2*n) ((n+10)*n^5)

end OrderSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalSplit
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
open BooleanNetwork Exactness
namespace FixedSplit

def ordersLayout (n : ℕ) : (Fin (n^5)→OrderSlots.Result n)≃Basis (ordersWidth n) :=
  (Equiv.piCongrRight (fun _ => OrderSlots.layout n)).trans (tensorLayout (OrderSlots.width n) (n^5))
def ordersProgram (n : ℕ) : List (Instruction (ordersWidth n)) := tensorProgram (OrderSlots.program n) (n^5)

def listWires (n : ℕ) : BooleanNetwork (PhysicalListSlots.launchWidth n) (PhysicalListSlots.width n) :=
  select (targetRegister n (PhysicalListSlots.width n) (PhysicalListSlots.work n))
def modulusWires (n : ℕ) : BooleanNetwork (PhysicalListSlots.launchWidth n) n :=
  select (firstRegister n (PhysicalListSlots.width n) (PhysicalListSlots.work n))
def listEncoding {n : ℕ} (m : Basis n) (l : PhysicalListSlots.Result n) : Basis (PhysicalListSlots.launchWidth n) :=
  packed (PhysicalListSlots.work n) m (PhysicalListSlots.layout n l)

def baseNet {n : ℕ} (i : Fin (n^5)) : BooleanNetwork (PhysicalListSlots.launchWidth n) n :=
  ((listWires n).comp (PhysicalListSlots.outputNet n)).rewire
    (fun j=>Fin.cast (Nat.mul_comm _ _) (finProdFinEquiv (i.castSucc,j)))

def orderInitialNet {n : ℕ} (i : Fin (n^5)) :
    BooleanNetwork (PhysicalListSlots.launchWidth n) (OrderSlots.width n) :=
  ((baseNet i).pair (modulusWires n)).comp (OrderSlots.initialNet n)

def ordersInitialNet (n : ℕ) : BooleanNetwork (PhysicalListSlots.launchWidth n) (ordersWidth n) :=
  tensorNetwork (fun i=>orderInitialNet (n:=n) i)

abbrev work (n : ℕ) := (ordersInitialNet n).net.count
abbrev width (n : ℕ) := PhysicalListSlots.launchWidth n+ordersWidth n+work n
/-- One actual fixed-gate circuit: the completed random list is generated first;
only that same list supplies the bases for the ensuing order slots. -/
def program (n : ℕ) : List (Instruction (width n)) :=
  appendPrepared (PhysicalListSlots.launch n) (ordersInitialNet n) le_rfl (ordersProgram n)
def encoding {n : ℕ} (m : Basis n) (r : Raw n) : Basis (width n) :=
  packed (work n) (listEncoding m r.1) (ordersLayout n r.2)
def zero {n : ℕ} (m : Basis n) : Basis (width n) :=
  packed (work n) (packed (PhysicalListSlots.work n) m (fun _=>false)) (fun _=>false)

end FixedSplit
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalSplitLaunch
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

namespace FixedSplit

def initialNet (n : ℕ) : BooleanNetwork n (width n) :=
  packNet (work n)
    (packNet (PhysicalListSlots.work n) (select id) (Completion.zeros n (PhysicalListSlots.width n)))
    (Completion.zeros n (ordersWidth n))

end FixedSplit
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalMachine
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
open BooleanNetwork RecordedHistory

/-- A bit-level finite-state controller. Both transition functions are literal
Boolean networks; this structure does not grant any classical computation oracle. -/
structure SplitMachine (n c : ℕ) where
  query : BooleanNetwork c n
  update : BooleanNetwork (c+FixedSplit.width n) c

namespace SplitMachine
variable {n c : ℕ} (M : SplitMachine n c)

abbrev initWork := M.query.net.count+(FixedSplit.initialNet n).net.count
abbrev updateWork := M.update.net.count

abbrev width : ℕ→ℕ
  | 0=>c
  | t+1=>(width t+FixedSplit.width n+M.initWork)+c+M.updateWork

def current : (t : ℕ)→Register c (M.width t)
  | 0=>⟨id,Function.injective_id⟩
  | t+1=>targetRegister (M.width t+FixedSplit.width n+M.initWork) c M.updateWork

def currentNet (t : ℕ) : BooleanNetwork (M.width t) c := select (M.current t)
def initNet (t : ℕ) : BooleanNetwork (M.width t) (FixedSplit.width n) :=
  ((M.currentNet t).comp M.query).comp (FixedSplit.initialNet n)
lemma initNet_count (t : ℕ) : (M.initNet t).net.count=M.initWork := by
  simp only [initNet,count_comp,currentNet,count_select,zero_add]

def updateNet (t : ℕ) : BooleanNetwork (M.width t+FixedSplit.width n+M.initWork) c :=
  (((select (firstRegister (M.width t) (FixedSplit.width n) M.initWork)).comp
    (M.currentNet t)).pair (select (targetRegister (M.width t) (FixedSplit.width n) M.initWork))).comp M.update
lemma updateNet_count (t : ℕ) : (M.updateNet t).net.count=M.updateWork := by
  simp only [updateNet,count_comp,count_pair,count_select,currentNet,zero_add]

def program : (t : ℕ)→List (Instruction (M.width t))
  | 0=>[]
  | t+1=>firstProgram c M.updateWork
      (appendPrepared (program t) (M.initNet t) (M.initNet_count t).le (FixedSplit.program n))++
      oracleOn (M.updateNet t) (M.updateNet_count t).le

def initial : (t : ℕ)→Basis c→Basis (M.width t)
  | 0,x=>x
  | t+1,x=>packed M.updateWork (packed M.initWork (initial t x) (fun _=>false)) (fun _=>false)

abbrev Trace (n : ℕ) : ℕ→Type
  | 0=>Unit
  | t+1=>Trace n t×FixedSplit.Raw n
noncomputable instance traceFintype (n t : ℕ) : Fintype (Trace n t) := by
  induction t with
  | zero=>exact inferInstanceAs (Fintype Unit)
  | succ t ih=>letI:=ih;exact inferInstanceAs (Fintype (Trace n t×FixedSplit.Raw n))

def next (x : Basis c) (r : FixedSplit.Raw n) : Basis c :=
  M.update.eval (Fin.append x (FixedSplit.encoding (M.query.eval x) r))
def config (x : Basis c) : (t : ℕ)→Trace n t→Basis c
  | 0,_=>x
  | t+1,h=>M.next (config x t h.1) h.2

def encoded (x : Basis c) : (t : ℕ)→Trace n t→Basis (M.width t)
  | 0,_=>x
  | t+1,h=>packed M.updateWork
      (packed M.initWork (encoded x t h.1)
        (FixedSplit.encoding (M.query.eval (M.config x t h.1)) h.2)) (M.config x (t+1) h)
noncomputable def state (x : Basis c) : (t : ℕ)→Trace n t→ℂ
  | 0,_=>1
  | t+1,h=>state x t h.1*FixedSplit.fresh (M.query.eval (M.config x t h.1)) h.2

end SplitMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalMachineMass
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
open Exactness RecordedHistory
namespace SplitMachine
variable {n c : ℕ} (M : SplitMachine n c)

/-- Filtering the actual chronological query at each clock tick. No collection
of answers for unselected/counterfactual moduli occurs in this predicate. -/
noncomputable def passed (x : Basis c) : (t : ℕ)→Trace n t→Prop
  | 0,_=>True
  | t+1,h=>passed x t h.1 ∧ UniversalSplit.passed (M.query.eval (M.config x t h.1)) h.2

end SplitMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_MachineInitialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace SplitMachine
variable {n c : ℕ} (M : SplitMachine n c)

/-- Literal clean initialization: retain the runtime controller word and create
only zero history/output/scratch fields. No query result is precomputed. -/
def initialNet : (t : ℕ) → BooleanNetwork c (M.width t)
  | 0 => select id
  | t+1 => packNet M.updateWork
      (packNet M.initWork (initialNet t) (Completion.zeros c (FixedSplit.width n)))
      (Completion.zeros c c)

end SplitMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeControlCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

def properOn {k w : ℕ} (m d : BooleanNetwork k w) : BooleanNetwork k 1 :=
  ((wordLt (wordConstant (BitVec.ofNat w 1)) d).band (wordLt d m)).band
    (zeroWord ((m.pair d).comp (mod w)))

namespace NodeCircuit

def popped (s w : ℕ) : BooleanNetwork (width s w) ((s+1)*w) :=
  (pending s w).comp (stackPop (s+1) w)
def quotient (s w : ℕ) : BooleanNetwork (width s w) w :=
  ((top s w).pair (divisor s w)).comp (div w)
def isPrime (s w : ℕ) : BooleanNetwork (width s w) 1 := (top s w).comp (primeWord w)
def isDone (s w : ℕ) : BooleanNetwork (width s w) 1 := zeroWord (top s w)
def isProper (s w : ℕ) : BooleanNetwork (width s w) 1 := properOn (top s w) (divisor s w)
def split (s w : ℕ) : BooleanNetwork (width s w) ((s+1)*w) :=
  stackPush (divisor s w) (stackPush (quotient s w) (popped s w))

def next (s w : ℕ) : BooleanNetwork (width s w) ((s+1)*w) :=
  wordMux (isDone s w) (pending s w)
    (wordMux (isPrime s w) (popped s w) (wordMux (isProper s w) (split s w) (pending s w)))
def emitted (s w : ℕ) : BooleanNetwork (width s w) w :=
  wordMux (isPrime s w) (top s w) (wordConstant 0)
def failed (s w : ℕ) : BooleanNetwork (width s w) 1 :=
  ((isDone s w).bnot.band (isPrime s w).bnot).band (isProper s w).bnot

def pack {s w : ℕ} (xs : List (Basis w)) (d : Basis w) : Basis (width s w) :=
  Fin.append (stackEncoding (s+1) w xs) d

@[simp] lemma pending_pack {s w : ℕ} (xs : List (Basis w)) (d : Basis w) :
    (pending s w).eval (pack xs d)=stackEncoding (s+1) w xs := by
  funext i
  exact Fin.append_left _ _ i
@[simp] lemma divisor_pack {s w : ℕ} (xs : List (Basis w)) (d : Basis w) :
    (divisor s w).eval (pack xs d)=d := by
  funext i
  exact Fin.append_right _ _ i

end NodeCircuit
end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeStateCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.ControlledTranslation.dataPart_append _root_.OAI.ExactQuantumFactoring.ControlledTranslation.phasePart_append _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

def pending (s w : ℕ) : BooleanNetwork (width s w) ((s+1)*w) :=
  select ((Fin.castAdd 1) ∘ (Fin.castAdd ((s+1)*w)))
def output (s w : ℕ) : BooleanNetwork (width s w) ((s+1)*w) :=
  select ((Fin.castAdd 1) ∘ (Fin.natAdd ((s+1)*w)))
def bad (s w : ℕ) : BooleanNetwork (width s w) 1 :=
  select (Fin.natAdd ((s+1)*w+(s+1)*w))
def top (s w : ℕ) : BooleanNetwork (width s w) w := (pending s w).comp (blockNet (s+1) w 0)
def old (s w : ℕ) : BooleanNetwork (inWidth s w) (width s w) := select (Fin.castAdd w)
def supplied (s w : ℕ) : BooleanNetwork (inWidth s w) w := select (Fin.natAdd (width s w))
def nodeInput (s w : ℕ) : BooleanNetwork (inWidth s w) (NodeCircuit.width s w) :=
  ((old s w).comp (pending s w)).pair (supplied s w)
def nextPending (s w : ℕ) : BooleanNetwork (inWidth s w) ((s+1)*w) :=
  (nodeInput s w).comp (NodeCircuit.next s w)
def emission (s w : ℕ) : BooleanNetwork (inWidth s w) w :=
  (nodeInput s w).comp (NodeCircuit.emitted s w)
def nextOutput (s w : ℕ) : BooleanNetwork (inWidth s w) ((s+1)*w) :=
  wordMux (zeroWord (emission s w)) ((old s w).comp (output s w))
    (stackPush (emission s w) ((old s w).comp (output s w)))
def nextBad (s w : ℕ) : BooleanNetwork (inWidth s w) 1 :=
  ((old s w).comp (bad s w)).bor ((nodeInput s w).comp (NodeCircuit.failed s w))
def step (s w : ℕ) : BooleanNetwork (inWidth s w) (width s w) :=
  ((nextPending s w).pair (nextOutput s w)).pair (nextBad s w)

def pack {s w : ℕ} (xs ys : List (Basis w)) (bad : Bool) : Basis (width s w) :=
  Fin.append (Fin.append (stackEncoding (s+1) w xs) (stackEncoding (s+1) w ys)) (fun _=>bad)

@[simp] lemma pending_pack {s w : ℕ} (xs ys : List (Basis w)) (b : Bool) :
    (pending s w).eval (pack xs ys b)=stackEncoding (s+1) w xs := by
  funext i
  simp [pending,eval_select,pack]
@[simp] lemma output_pack {s w : ℕ} (xs ys : List (Basis w)) (b : Bool) :
    (output s w).eval (pack xs ys b)=stackEncoding (s+1) w ys := by
  funext i
  rw [output,eval_select]
  change Fin.append (Fin.append (stackEncoding (s+1) w xs) (stackEncoding (s+1) w ys))
    (fun _=>b) (Fin.castAdd 1 (Fin.natAdd ((s+1)*w) i))=_
  rw [Fin.append_left,Fin.append_right]
@[simp] lemma bad_pack {s w : ℕ} (xs ys : List (Basis w)) (b : Bool) :
    (bad s w).eval (pack xs ys b)=(fun _=>b) := by
  funext i
  simp [bad,eval_select,pack]

end NodeStateCircuit
end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SamplerDecodeCircuit
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
namespace BooleanNetwork

def leftNet (u v : ℕ) : BooleanNetwork (u+v) u := select (Fin.castAdd v)
def rightNet (u v : ℕ) : BooleanNetwork (u+v) v := select (Fin.natAdd u)

end BooleanNetwork
namespace OrderTrial

def sampleYNet (u b : ℕ) : BooleanNetwork (OrderSample.width u b) b :=
  select (fun i => (((Fin.natAdd (u+u) (Triangular.dataWire i)).castAdd u).castAdd (OrderSample.scratch u b)))
def sampleUNet (u b : ℕ) : BooleanNetwork (OrderSample.width u b) u :=
  select (fun i => ((Fin.natAdd (OrderSample.inputWidth u b) i).castAdd (OrderSample.scratch u b)))

def triangularSelectedNet {k b : ℕ} (y : BooleanNetwork k b) : BooleanNetwork k (Triangular.width b) :=
  packNet (Triangular.work b) (y.pair (Completion.zeros k b)) (Completion.zeros k (b+b))

/-- Full selection compares retained read-only inputs and every sampler scratch
bit, not only the apparent phase and modular residue fields. -/
def samplerSelectedNet {k u b : ℕ} (a m : BooleanNetwork k u)
    (z : BooleanNetwork k (OrderSample.width u b)) : BooleanNetwork k 1 :=
  equalOn z (packNet (OrderSample.scratch u b)
    ((a.pair m).pair (triangularSelectedNet (z.comp (sampleYNet u b))))
    (z.comp (sampleUNet u b)))

end OrderTrial
end ExactQuantumFactoring


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

def minimumChoice (w : ℕ) : BooleanNetwork (w+w) w :=
  let a := leftNet w w
  let b := rightNet w w
  wordMux (equalOn a (wordConstant (BitVec.ofNat w 0))) b
    (wordMux (equalOn b (wordConstant (BitVec.ofNat w 0))) a (wordMux (wordLt a b) a b))

/-- Pair costly subnets ONCE before comparing; the recursive minimum is not
copied into each arm of the mux. This gives a linear, not exponential, scan. -/
def minimumNet {k w : ℕ} : {K : ℕ} → (Fin K → BooleanNetwork k w) → BooleanNetwork k w
  | 0,_ => wordConstant (BitVec.ofNat w 0)
  | _+1,f => ((f 0).pair (minimumNet (fun i => f i.succ))).comp (minimumChoice w)

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RawTrialFields
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

def rawMode {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k 2 :=
  r.comp (leftNet 2 (OrderSample.width u (s+2)+guessWidth n))
def rawSample {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    BooleanNetwork k (OrderSample.width u (s+2)) :=
  (r.comp (rightNet 2 (OrderSample.width u (s+2)+guessWidth n))).comp
    (leftNet (OrderSample.width u (s+2)) (guessWidth n))
def rawGuesses {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k (guessWidth n) :=
  (r.comp (rightNet 2 (OrderSample.width u (s+2)+guessWidth n))).comp
    (rightNet (OrderSample.width u (s+2)) (guessWidth n))
def rawDen {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k n :=
  (rawGuesses r).comp (leftNet n (n+(n+retentionBits n)))
def rawNum {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k n :=
  ((rawGuesses r).comp (rightNet n (n+(n+retentionBits n)))).comp (leftNet n (n+retentionBits n))
def rawResidue {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k n :=
  (((rawGuesses r).comp (rightNet n (n+(n+retentionBits n)))).comp
    (rightNet n (n+retentionBits n))).comp (leftNet n (retentionBits n))
def rawCoin {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k (retentionBits n) :=
  (((rawGuesses r).comp (rightNet n (n+(n+retentionBits n)))).comp
    (rightNet n (n+retentionBits n))).comp (rightNet n (retentionBits n))

def toWidth {k u : ℕ} (w : ℕ) (a : BooleanNetwork k u) : BooleanNetwork k w :=
  a.comp (resizeWord u w)

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

def recoveredPairNet {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    BooleanNetwork k (decodeWidth u s n+decodeWidth u s n) :=
  recoveryNet (wordConstant (BitVec.ofNat (decodeWidth u s n) (2^(s+2))))
    (wordConstant (BitVec.ofNat (decodeWidth u s n) (2^n)))
    (toWidth (decodeWidth u s n) ((rawSample r).comp (sampleYNet u (s+2)))) (decodeSteps s)

def trialPairNet {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    BooleanNetwork k (decodeWidth u s n+decodeWidth u s n) :=
  wordMux (wordLt (toWidth (decodeWidth u s n) (rawMode r))
      (wordConstant (BitVec.ofNat (decodeWidth u s n) 2)))
    (recoveredPairNet r)
    ((toWidth (decodeWidth u s n) (rawDen r)).pair (toWidth (decodeWidth u s n) (rawNum r)))
def trialDenNet {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    BooleanNetwork k (decodeWidth u s n) :=
  (trialPairNet r).comp (leftNet (decodeWidth u s n) (decodeWidth u s n))
def trialNumNet {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    BooleanNetwork k (decodeWidth u s n) :=
  (trialPairNet r).comp (rightNet (decodeWidth u s n) (decodeWidth u s n))

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_LabelValidationCircuit
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

/-- Every returned denominator, in EVERY mode, undergoes the full arithmetic
check. No primality or order oracle appears in the network. -/
def labelValidNet {k w : ℕ} (n : ℕ) (a m d j : BooleanNetwork k w) : BooleanNetwork k 1 :=
  (wordLt (wordConstant (BitVec.ofNat w 0)) d).band
    ((wordLt d (wordConstant (BitVec.ofNat w (2^n)))).band
      ((wordLt j d).band
        ((equalOn ((j.pair d).comp (gcdNet w)) (wordConstant (BitVec.ofNat w 1))).band
          (equalOn (powOn a m d) (wordConstant (BitVec.ofNat w 1))))))

end ExactQuantumFactoring.OrderTrial


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

/-- Compile the dyadic threshold to a finite Boolean network. All arithmetic,
including signed rational division and floor, is reduced to bounded word gates. -/
def retentionNet {v : Type*} {k b : ℕ} (T : ℕ) (p : RatExpr v) (coin : NatExpr v)
    (vars : v → BooleanNetwork k b) : BooleanNetwork k 1 :=
  (thresholdExpr T p coin).isOne vars
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

def decodeVars {k w : ℕ} (d j t c : BooleanNetwork k w) : DecodeVar → BooleanNetwork k w
  | .den => d | .num => j | .residue => t | .coin => c

def firstRetNet {k w : ℕ} (n : ℕ) (d j t c : BooleanNetwork k w) : BooleanNetwork k 1 :=
  retentionNet (retentionBits n) (Expressions.firstE n (.var .den) (.var .num))
    (.var .coin) (decodeVars d j t c)
def secondRetNet {k w : ℕ} (n : ℕ) (d j t c : BooleanNetwork k w) : BooleanNetwork k 1 :=
  retentionNet (retentionBits n) (Expressions.secondE n (.var .den) (.var .num) (.var .residue))
    (.var .coin) (decodeVars d j t c)
def thirdRetNet {k w : ℕ} (n : ℕ) (d j t c : BooleanNetwork k w) : BooleanNetwork k 1 :=
  retentionNet (retentionBits n) (Expressions.lastE n (.var .den) (.var .num))
    (.var .coin) (decodeVars d j t c)

/-- Mode guards are outside the rational computations. In particular malformed
labels and residue guesses cannot turn an irrelevant retention into acceptance. -/
def trialAcceptOn {k w : ℕ} (n : ℕ) (a m mode d j t c : BooleanNetwork k w)
    (selected : BooleanNetwork k 1) : BooleanNetwork k 1 :=
  (labelValidNet n a m d j).band
    (((wordLt mode (wordConstant (BitVec.ofNat w 2))).band
      (selected.band (firstRetNet n d j t c))).bor
    (((equalOn mode (wordConstant (BitVec.ofNat w 2))).band
      ((wordLt t d).band (secondRetNet n d j t c))).bor
     ((equalOn mode (wordConstant (BitVec.ofNat w 3))).band (thirdRetNet n d j t c))))

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RawTrialDecoder
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

/-- Exact ordinary trial decoder, including the sampler's full workspace test,
continued-fraction reconstruction, arithmetic validation, and all three retained
coin tests. Its inputs are actual retained raw bits. -/
def rawAcceptNet {k u s n : ℕ} (a m : BooleanNetwork k u)
    (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k 1 :=
  trialAcceptOn n (toWidth (decodeWidth u s n) a) (toWidth (decodeWidth u s n) m)
    (toWidth (decodeWidth u s n) (rawMode r)) (trialDenNet r) (trialNumNet r)
    (toWidth (decodeWidth u s n) (rawResidue r)) (toWidth (decodeWidth u s n) (rawCoin r))
    (samplerSelectedNet a m (rawSample r))

def trialValueNet {k u s n : ℕ} (a m : BooleanNetwork k u)
    (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k (decodeWidth u s n) :=
  wordMux (rawAcceptNet a m r) (trialDenNet r) (wordConstant (BitVec.ofNat (decodeWidth u s n) 0))

/-- Only VALID ordinary candidates are narrowed to n bits. This does not apply
to the separately completed rare guess, whose whole transition word is kept. -/
def trialSmallValueNet {k u s n : ℕ} (a m : BooleanNetwork k u)
    (r : BooleanNetwork k (rawWidth u s n)) : BooleanNetwork k n :=
  (trialValueNet a m r).comp (resizeWord (decodeWidth u s n) n)

end ExactQuantumFactoring.OrderTrial


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalOrderDecoder
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

namespace OrderSlots

def usableOn {k n : ℕ} (a m : BooleanNetwork k n) : BooleanNetwork k 1 :=
  (wordLt a m).band (equalOn ((a.pair m).comp (gcdNet n)) (wordConstant (BitVec.ofNat n 1)))

/-- Every ordinary raw trial uses its actual tensor block. Nonempty candidates
are validated before a shared, linear-size least-positive-candidate fold. -/
def orderResultNet {k n : ℕ} (a m : BooleanNetwork k n)
    (raw : BooleanNetwork k (ordinaryWidth n)) : BooleanNetwork k n :=
  minimumNet (fun i : Fin (n^5) => trialSmallValueNet a m
    (raw.comp (tensorSelect (rawWidth n (sampleExponent n) n) (n^5) i)))

def ordinaryOn {k n : ℕ} (a m : BooleanNetwork k n)
    (raw : BooleanNetwork k (ordinaryWidth n)) : BooleanNetwork k (Completion.transitionWidth n) :=
  (wordMux (usableOn a m) (orderResultNet a m raw) (wordConstant (BitVec.ofNat n 0))).comp
    (resizeWord n (Completion.transitionWidth n))

/-- Completed output decoding keeps the FULL rare guessed transition word. No
truncation, success flag, or later true-order certificate enters this decoder. -/
def outputOn {k n : ℕ} (a m : BooleanNetwork k n) (raw : BooleanNetwork k (width n)) :
    BooleanNetwork k (Completion.transitionWidth n) :=
  wordMux (raw.comp (Completion.rareNet (ordinaryWidth n) (Completion.transitionWidth n) (2*n) ((n+10)*n^5)))
    (raw.comp (Completion.guessWires (ordinaryWidth n) (Completion.transitionWidth n) (2*n) ((n+10)*n^5)))
    (ordinaryOn a m (raw.comp (Completion.ordinaryWires (ordinaryWidth n) (Completion.transitionWidth n) (2*n) ((n+10)*n^5))))

end OrderSlots
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SuppliedDivisorCircuit
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

namespace BitArithmetic
open BooleanNetwork FactorController

def firstProperNet {k w : ℕ} (m : BooleanNetwork k w) :
    List (BooleanNetwork k w) → BooleanNetwork k w
  | [] => wordConstant 0
  | d::ds => wordMux (properOn m d) d (firstProperNet m ds)

def evenOn {k w : ℕ} (m : BooleanNetwork k w) : BooleanNetwork k 1 :=
  zeroWord ((m.pair (wordConstant (BitVec.ofNat w 2))).comp (mod w))

def rootOn {k : ℕ} (n e : ℕ) (m : BooleanNetwork k (n+1)) : BooleanNetwork k (n+1) :=
  ((m.comp (resizeWord (n+1) (rootWidth n))).comp (boundedRootNet n e)).comp
    (resizeWord (rootWidth n) (n+1))

def rootsOn {k : ℕ} (n : ℕ) (m : BooleanNetwork k (n+1)) : BooleanNetwork k (n+1) :=
  firstProperNet m ((List.range (n+1)).map (fun e => rootOn n e m))

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_WideSplitCircuit
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

/-- The exponent word may be the entire completion-guess width. In particular
an arbitrary rare-branch guess is NOT silently truncated to n bits. -/
def halfPowerBits {k w e : ℕ} (a m : BooleanNetwork k w) (d : BooleanNetwork k e) : BooleanNetwork k w :=
  ((a.pair m).pair ((halfWord d).rewire Fin.rev)).comp (modularPower w e)

def shiftedHalfBits {k w e : ℕ} (a m : BooleanNetwork k w) (d : BooleanNetwork k e) : BooleanNetwork k w :=
  ((((halfPowerBits a m d).pair m).comp (add w)).pair
    (wordConstant (BitVec.ofNat w 1))).comp (sub w)

def candidateBits {k w e : ℕ} (a m : BooleanNetwork k w) (d : BooleanNetwork k e) : BooleanNetwork k w :=
  wordMux ((zeroWord d).bnot.band (evenOn d))
    (((shiftedHalfBits a m d).pair m).comp (gcdNet w)) (wordConstant 0)

def ordersBits {k w e : ℕ} (m : BooleanNetwork k w)
    (ars : List (BooleanNetwork k w × BooleanNetwork k e)) : BooleanNetwork k w :=
  firstProperNet m (ars.map (fun ar => candidateBits ar.1 m ar.2))

def suppliedBits {k e : ℕ} (n : ℕ) (m : BooleanNetwork k (n+1))
    (ars : List (BooleanNetwork k (n+1) × BooleanNetwork k e)) : BooleanNetwork k (n+1) :=
  wordMux (evenOn m) (wordConstant (BitVec.ofNat (n+1) 2))
    (wordMux (properOn m (rootsOn n m)) (rootsOn n m) (ordersBits m ars))

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalSplitDecoder
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
namespace FixedSplit

def launchWires (n : ℕ) : BooleanNetwork (width n) (PhysicalListSlots.launchWidth n) :=
  select (firstRegister (PhysicalListSlots.launchWidth n) (ordersWidth n) (work n))
def allOrderWires (n : ℕ) : BooleanNetwork (width n) (ordersWidth n) :=
  select (targetRegister (PhysicalListSlots.launchWidth n) (ordersWidth n) (work n))
def modulusNet (n : ℕ) : BooleanNetwork (width n) n := (launchWires n).comp (modulusWires n)
def actualBaseNet {n : ℕ} (i : Fin (n^5)) : BooleanNetwork (width n) n :=
  (launchWires n).comp (baseNet i)
def actualOrderRawNet {n : ℕ} (i : Fin (n^5)) : BooleanNetwork (width n) (OrderSlots.width n) :=
  (allOrderWires n).comp (tensorSelect (OrderSlots.width n) (n^5) i)
def actualOrderNet {n : ℕ} (i : Fin (n^5)) : BooleanNetwork (width n) (Completion.transitionWidth n) :=
  OrderSlots.outputOn (actualBaseNet i) (modulusNet n) (actualOrderRawNet i)

def liftedModulus (n : ℕ) : BooleanNetwork (width n) (n+1) :=
  (modulusNet n).comp (resizeWord n (n+1))
def actualPairs (n : ℕ) : List (BooleanNetwork (width n) (n+1) ×
    BooleanNetwork (width n) (Completion.transitionWidth n)) :=
  List.ofFn (fun i : Fin (n^5) => ((actualBaseNet i).comp (resizeWord n (n+1)),actualOrderNet i))

/-- Supplied divisor computed from exactly this run's retained quantum bits.
All guarded arithmetic is explicit, including full rare-branch order guesses. -/
def divisorNet (n : ℕ) : BooleanNetwork (width n) (n+1) :=
  suppliedBits n (liftedModulus n) (actualPairs n)

end FixedSplit
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeSplitMachine
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
open BooleanNetwork BitArithmetic
namespace PhysicalNode

abbrev configWidth (n s : ℕ) := NodeStateCircuit.width s (n+1)
def query (n s : ℕ) : BooleanNetwork (configWidth n s) n :=
  (NodeStateCircuit.top s (n+1)).comp (resizeWord (n+1) n)
def update (n s : ℕ) : BooleanNetwork (configWidth n s+FixedSplit.width n) (configWidth n s) :=
  ((select (Fin.castAdd (FixedSplit.width n))).pair
    ((select (Fin.natAdd (configWidth n s))).comp (FixedSplit.divisorNet n))).comp
      (NodeStateCircuit.step s (n+1))
def machine (n s : ℕ) : SplitMachine n (configWidth n s) := ⟨query n s,update n s⟩
def decoded {n : ℕ} (q : Basis n) (r : FixedSplit.Raw n) : Basis (n+1) :=
  (FixedSplit.divisorNet n).eval (FixedSplit.encoding q r)

end PhysicalNode
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalNodeLaunch
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
namespace PhysicalNode

/-- The node's initial pending stack contains only the runtime modulus, enlarged
by one bit. Emission and error registers are zero. No factor data is supplied. -/
def startNet (n : ℕ) : BooleanNetwork n (configWidth n (2*n)) :=
  ((stackPush (resizeWord n (n+1))
      (Completion.zeros n ((2*n+1)*(n+1)))).pair
    (Completion.zeros n ((2*n+1)*(n+1)))).pair (constant false)

abbrev runWidth (n : ℕ) := (machine n (2*n)).width (2*n)
def runInitial (n : ℕ) : BooleanNetwork n (runWidth n) :=
  (startNet n).comp ((machine n (2*n)).initialNet (2*n))

end PhysicalNode
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalNodeKernel
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
open BooleanNetwork
namespace NodeKernel
abbrev width (n : ℕ) := PhysicalNode.runWidth n
abbrev Raw (n : ℕ) := SplitMachine.Trace n (2*n)
def initialNet (n : ℕ) : BooleanNetwork n (width n) := PhysicalNode.runInitial n
def start {n : ℕ} (q : Basis n) := (PhysicalNode.startNet n).eval q
def zero {n : ℕ} (q : Basis n) : Basis (width n) :=
  (PhysicalNode.machine n (2*n)).initial (2*n) (start q)
def encoding {n : ℕ} (q : Basis n) (r : Raw n) : Basis (width n) :=
  (PhysicalNode.machine n (2*n)).encoded (start q) (2*n) r
noncomputable def fresh {n : ℕ} (q : Basis n) (r : Raw n) : ℂ :=
  (PhysicalNode.machine n (2*n)).state (start q) (2*n) r
def program (n : ℕ) : List (Instruction (width n)) :=
  (PhysicalNode.machine n (2*n)).program (2*n)
noncomputable def passed {n : ℕ} (q : Basis n) (r : Raw n) : Prop :=
  (PhysicalNode.machine n (2*n)).passed (start q) (2*n) r
end NodeKernel
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalTreeMachine
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
open BooleanNetwork RecordedHistory

/-- A bit-level finite-state controller. Both transition functions are literal
Boolean networks; this structure does not grant any classical computation oracle. -/
structure NodeMachine (n c : ℕ) where
  query : BooleanNetwork c n
  update : BooleanNetwork (c+NodeKernel.width n) c

namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

abbrev initWork := M.query.net.count+(NodeKernel.initialNet n).net.count
abbrev updateWork := M.update.net.count

abbrev width : ℕ→ℕ
  | 0=>c
  | t+1=>(width t+NodeKernel.width n+M.initWork)+c+M.updateWork

def current : (t : ℕ)→Register c (M.width t)
  | 0=>⟨id,Function.injective_id⟩
  | t+1=>targetRegister (M.width t+NodeKernel.width n+M.initWork) c M.updateWork

def currentNet (t : ℕ) : BooleanNetwork (M.width t) c := select (M.current t)
def initNet (t : ℕ) : BooleanNetwork (M.width t) (NodeKernel.width n) :=
  ((M.currentNet t).comp M.query).comp (NodeKernel.initialNet n)
lemma initNet_count (t : ℕ) : (M.initNet t).net.count=M.initWork := by
  simp only [initNet,count_comp,currentNet,count_select,zero_add]

def updateNet (t : ℕ) : BooleanNetwork (M.width t+NodeKernel.width n+M.initWork) c :=
  (((select (firstRegister (M.width t) (NodeKernel.width n) M.initWork)).comp
    (M.currentNet t)).pair (select (targetRegister (M.width t) (NodeKernel.width n) M.initWork))).comp M.update
lemma updateNet_count (t : ℕ) : (M.updateNet t).net.count=M.updateWork := by
  simp only [updateNet,count_comp,count_pair,count_select,currentNet,zero_add]

def program : (t : ℕ)→List (Instruction (M.width t))
  | 0=>[]
  | t+1=>firstProgram c M.updateWork
      (appendPrepared (program t) (M.initNet t) (M.initNet_count t).le (NodeKernel.program n))++
      oracleOn (M.updateNet t) (M.updateNet_count t).le

def initial : (t : ℕ)→Basis c→Basis (M.width t)
  | 0,x=>x
  | t+1,x=>packed M.updateWork (packed M.initWork (initial t x) (fun _=>false)) (fun _=>false)

abbrev Trace (n : ℕ) : ℕ→Type
  | 0=>Unit
  | t+1=>Trace n t×NodeKernel.Raw n
noncomputable instance traceFintype (n t : ℕ) : Fintype (Trace n t) := by
  induction t with
  | zero=>exact inferInstanceAs (Fintype Unit)
  | succ t ih=>letI:=ih;exact inferInstanceAs (Fintype (Trace n t×NodeKernel.Raw n))

def next (x : Basis c) (r : NodeKernel.Raw n) : Basis c :=
  M.update.eval (Fin.append x (NodeKernel.encoding (M.query.eval x) r))
def config (x : Basis c) : (t : ℕ)→Trace n t→Basis c
  | 0,_=>x
  | t+1,h=>M.next (config x t h.1) h.2

def encoded (x : Basis c) : (t : ℕ)→Trace n t→Basis (M.width t)
  | 0,_=>x
  | t+1,h=>packed M.updateWork
      (packed M.initWork (encoded x t h.1)
        (NodeKernel.encoding (M.query.eval (M.config x t h.1)) h.2)) (M.config x (t+1) h)
noncomputable def state (x : Basis c) : (t : ℕ)→Trace n t→ℂ
  | 0,_=>1
  | t+1,h=>state x t h.1*NodeKernel.fresh (M.query.eval (M.config x t h.1)) h.2

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalTreeMass
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
open Exactness RecordedHistory
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

/-- Filtering the actual chronological query at each clock tick. No collection
of answers for unselected/counterfactual moduli occurs in this predicate. -/
noncomputable def passed (x : Basis c) : (t : ℕ)→Trace n t→Prop
  | 0,_=>True
  | t+1,h=>passed x t h.1 ∧ NodeKernel.passed (M.query.eval (M.config x t h.1)) h.2

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeProgress
attribute [-instance] _root_.OAI.ExactQuantumFactoring.BitArithmetic.SortedWords.instDecidableLEWord
attribute [-simp] _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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
open BooleanNetwork BitArithmetic FactorController
namespace PhysicalNode

def values {w : ℕ} (xs : List (Basis w)) : List ℕ := xs.map (fun x=>(bitsValue x).toNat)
@[simp] lemma values_nil (w : ℕ) : values ([] : List (Basis w))=[] := rfl
@[simp] lemma values_cons {w : ℕ} (a : Basis w) (xs : List (Basis w)) :
    values (a::xs)=(bitsValue a).toNat::values xs := rfl

structure Good (n N fuel : ℕ) (xs ys : List (Basis (n+1))) : Prop where
  bounded : ∀ a ∈ xs, 2 ≤ (bitsValue a).toNat ∧ (bitsValue a).toNat<2^n
  primes : ∀ a ∈ ys, (bitsValue a).toNat.Prime
  product : (values xs).prod*(values ys).prod=N
  clock : weight (values xs) ≤ fuel

end PhysicalNode
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SortingCircuit
attribute [-instance] _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
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
namespace SortedWords

def layout (w : ℕ) : (r : ℕ)→List (Basis w)→Basis (tensorWidth w r)
  | 0,_=>Fin.elim0
  | r+1,xs=>Fin.append (xs.head?.getD (fun _=>false)) (layout w r xs.tail)

def headNet (w r : ℕ) : BooleanNetwork (tensorWidth w (r+1)) w := select (Fin.castAdd (tensorWidth w r))
def tailNet (w r : ℕ) : BooleanNetwork (tensorWidth w (r+1)) (tensorWidth w r) := select (Fin.natAdd w)

/-- A recursive subnetwork is used ONCE, with its prefix wire retained. -/
def keepHead {w r : ℕ} (c : BooleanNetwork (tensorWidth w r) (tensorWidth w r)) :
    BooleanNetwork (tensorWidth w (r+1)) (tensorWidth w (r+1)) :=
  (headNet w r).pair ((tailNet w r).comp c)

def compareStep (w r : ℕ) : BooleanNetwork (tensorWidth w (r+2)) (tensorWidth w (r+2)) :=
  let a := headNet w (r+1)
  let b := (tailNet w (r+1)).comp (headNet w r)
  let rest := (tailNet w (r+1)).comp (tailNet w r)
  (wordMux (paddedPair a b) a b).pair ((wordMux (paddedPair a b) b a).pair rest)

def insertNet (w : ℕ) : (r : ℕ)→BooleanNetwork (tensorWidth w (r+1)) (tensorWidth w (r+1))
  | 0=>select id
  | r+1=>(compareStep w r).comp (keepHead (insertNet w r))
def sortNet (w : ℕ) : (r : ℕ)→BooleanNetwork (tensorWidth w r) (tensorWidth w r)
  | 0=>select id
  | r+1=>(keepHead (sortNet w r)).comp (insertNet w r)

end SortedWords
end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalNodeOutput
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
namespace PhysicalNode

def resultField (n : ℕ) (i : Fin n) : BooleanNetwork (configWidth n (2*n)) n :=
  ((NodeStateCircuit.output (2*n) (n+1)).comp
    (blockNet (2*n+1) (n+1) ⟨i.val,by omega⟩)).comp (resizeWord (n+1) n)

def sortedOutput (n : ℕ) : BooleanNetwork (configWidth n (2*n)) (tensorWidth n n) :=
  (tensorNetwork (resultField n)).comp (SortedWords.sortNet n n)

def shrink (n : ℕ) (a : Basis (n+1)) : Basis n := (resizeWord (n+1) n).eval a

end PhysicalNode
end ExactQuantumFactoring


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

def query (n : ℕ) : BooleanNetwork (configWidth n) n := blockNet (capacity n) n 0

def nodeResult (n : ℕ) : BooleanNetwork (NodeKernel.width n) (tensorWidth n n) :=
  ((PhysicalNode.machine n (2*n)).currentNet (2*n)).comp (PhysicalNode.sortedOutput n)
def fields (n : ℕ) : List (BooleanNetwork (NodeKernel.width n) n) :=
  List.ofFn (fun i : Fin n=>(nodeResult n).comp (tensorSelect n n i))

def old (n : ℕ) : BooleanNetwork (configWidth n+NodeKernel.width n) (configWidth n) :=
  select (Fin.castAdd (NodeKernel.width n))
def localNode (n : ℕ) : BooleanNetwork (configWidth n+NodeKernel.width n) (NodeKernel.width n) :=
  select (Fin.natAdd (configWidth n))
def pushed (n : ℕ) : BooleanNetwork (configWidth n+NodeKernel.width n) (configWidth n) :=
  (((localNode n).pair ((old n).comp (stackPop (capacity n) n))).comp
    (ChildQueue.pushAll (capacity n) (fields n))).comp
      (ChildQueue.queue (NodeKernel.width n) (capacity n) n)
/-- Literal fixed-capacity pending-node controller. The current modulus is
removed and this very node's distinct p−1 children are prepended in sorted order.
An empty queue is an idle tick, not a new root query. -/
def update (n : ℕ) : BooleanNetwork (configWidth n+NodeKernel.width n) (configWidth n) :=
  wordMux (zeroWord ((old n).comp (query n))) (old n) (pushed n)

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeHistoryAccess
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
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

/-- Access only retained earlier wires. No history is recomputed. -/
def previousNet (t : ℕ) : BooleanNetwork (M.width (t+1)) (M.width t) :=
  (select (firstRegister (M.width t+NodeKernel.width n+M.initWork) c M.updateWork)).comp
    (select (firstRegister (M.width t) (NodeKernel.width n) M.initWork))
def lastNodeNet (t : ℕ) : BooleanNetwork (M.width (t+1)) (NodeKernel.width n) :=
  (select (firstRegister (M.width t+NodeKernel.width n+M.initWork) c M.updateWork)).comp
    (select (targetRegister (M.width t) (NodeKernel.width n) M.initWork))

def firstNodeNet : (t : ℕ)→BooleanNetwork (M.width (t+1)) (NodeKernel.width n)
  | 0=>M.lastNodeNet 0
  | t+1=>(M.previousNet (t+1)).comp (firstNodeNet t)
def firstRaw : (t : ℕ)→Trace n (t+1)→NodeKernel.Raw n
  | 0,h=>h.2
  | t+1,h=>firstRaw t h.1

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeVerifiedCircuit
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

def resultFields (n : ℕ) : Fin n→BooleanNetwork (NodeKernel.width n) n :=
  fun i=>(nodeResult n).comp (tensorSelect n n i)
def nodeWords (n : ℕ) (z : Basis (NodeKernel.width n)) : List (Basis n) :=
  List.ofFn (fun i=>(resultFields n i).eval z)

def NodeVerified {n : ℕ} (q : Basis n) (r : NodeKernel.Raw n) : Prop :=
  (bitsValue q).toNat=0 ∨ CorrectEncoding (bitsValue q).toNat n
    (SortedWords.numbers (nodeWords n (NodeKernel.encoding q r)))

end PhysicalTree
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

def verified (x : Basis c) : (t : ℕ)→Trace n t→Prop
  | 0,_=>True
  | t+1,h=>verified x t h.1 ∧ PhysicalTree.NodeVerified
      (M.query.eval (M.config x t h.1)) h.2

def rowQuery (t : ℕ) : BooleanNetwork (M.width (t+1)) n :=
  ((M.previousNet t).comp (M.currentNet t)).comp M.query
def rowFields (t : ℕ) (i : Fin n) : BooleanNetwork (M.width (t+1)) n :=
  (M.lastNodeNet t).comp (PhysicalTree.resultFields n i)
def rowVerifiedNet (t : ℕ) : BooleanNetwork (M.width (t+1)) 1 :=
  (zeroWord (M.rowQuery t)).bor (factorVerifierOn (M.rowQuery t) (M.rowFields t))
def verifiedNet : (t : ℕ)→BooleanNetwork (M.width t) 1
  | 0=>constant true
  | t+1=>((M.previousNet t).comp (verifiedNet t)).band (M.rowVerifiedNet t)

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CanonicalWords
attribute [-instance] _root_.OAI.ExactQuantumFactoring.Completion.instDecidableRare
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
open OrderTrial SortedWords

def canonicalWords (n : ℕ) (xs : List ℕ) : List (Basis n) := xs.map (natBasis n)

end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_PhysicalTreeCompletion
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

def machine (n : ℕ) : NodeMachine n (configWidth n) := ⟨query n,update n⟩
def initialQueue (n N : ℕ) : Basis (configWidth n) :=
  stackEncoding (capacity n) n (canonicalWords n [N])

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
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

/-- Projection of the actual retained record, including dummy rows. No true
factorization is used in constructing this projection. -/
def dataLog (x : Basis c) : (t : ℕ)→Trace n t→List (ℕ×List ℕ)
  | 0,_=>[]
  | t+1,h=>
    let q:=M.query.eval (M.config x t h.1)
    ((bitsValue q).toNat,SortedWords.numbers
      (PhysicalTree.nodeWords n (NodeKernel.encoding q h.2)))::dataLog x t h.1
end NodeMachine
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

def dividesOn {k n : ℕ} (p m : BooleanNetwork k n) : BooleanNetwork k 1 :=
  zeroWord ((m.pair p).comp (mod n))

def leastDivisorTest {k n : ℕ} (ps : List (BooleanNetwork k n)) (m p : BooleanNetwork k n) :
    BooleanNetwork k 1 := all (ps.map (fun q=>(dividesOn q m).bnot.bor (wordLe p q)))

def componentCongruence {k n : ℕ} (ps : List (BooleanNetwork k n))
    (a m p : BooleanNetwork k n) : BooleanNetwork k 1 :=
  let q:=primeComponent m p
  equalOn ((a.pair q).comp (mod n)) (wordMux (leastDivisorTest ps m p)
    (wordConstant (BitVec.ofNat n 1)) (natSubOn q (wordConstant (BitVec.ofNat n 1))))

def tableCanonicalNet {k n : ℕ} (ps : List (BooleanNetwork k n))
    (a m : BooleanNetwork k n) : BooleanNetwork k 1 :=
  (wordLt a m).band (all (ps.map (fun p=>(dividesOn p m).bnot.bor (componentCongruence ps a m p))))

end BitArithmetic
end ExactQuantumFactoring


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
def gatePayload:=BitStackProgram.prodCode primitiveCode
  (BitStackProgram.prodCode BitStackProgram.Procedure.boolCode BitStackProgram.Procedure.boolCode)
def gateCode (g : Gate) : List Bool:=gatePayload (gateView g)
def opPayload:=BitStackProgram.prodCode gateCode (BitStackProgram.listCode Nat.bits)
def opCode (o : Op) : List Bool:=opPayload (opView o)
def dataPayload:=BitStackProgram.prodCode BitStackProgram.unaryCode (BitStackProgram.listCode opCode)
def dataCode (c : Data) : List Bool:=dataPayload (dataView c)

end ExactQuantumFactoring.CircuitEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CircuitEmissionEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Procedure
namespace Emission
noncomputable def gateViewP : Procedure gateCode gatePayload gateView:=
  (identity gatePayload).precompose gateView
noncomputable def gatePrimitiveP : Procedure gateCode primitiveCode Gate.primitive:=
  (first primitiveCode _).comp gateViewP
noncomputable def gateInverseP : Procedure gateCode boolCode Gate.inverse:=
  (first boolCode boolCode).comp ((second primitiveCode _).comp gateViewP)
noncomputable def gateControlledP : Procedure gateCode boolCode Gate.controlled:=
  (second boolCode boolCode).comp ((second primitiveCode _).comp gateViewP)
noncomputable def gateHeaderP : Procedure gateCode id
    (fun g=>natWord g.primitive.code++[g.inverse,g.controlled]) := by
  let primitiveWord:=(natWordP.precompose Primitive.code).comp gatePrimitiveP
  let c:=cons.comp (gateControlledP.pair (Procedure.constant gateCode id []))
  let tail:=cons.comp (gateInverseP.pair c)
  exact (append.comp (primitiveWord.pair tail)).congrFun (by intro g;rfl)
noncomputable def opViewP : Procedure opCode opPayload opView:=
  (identity opPayload).precompose opView
noncomputable def opGateP : Procedure opCode gateCode Op.gate:=
  (first gateCode (listCode Nat.bits)).comp opViewP
noncomputable def opWiresP : Procedure opCode (listCode Nat.bits) Op.wires:=
  (second gateCode (listCode Nat.bits)).comp opViewP
noncomputable def opEncodeClippedP : Procedure (prodCode unaryCode opCode) id
    (fun x=>x.2.encodeClipped x.1) := by
  let cap:=first unaryCode opCode
  let o:=second unaryCode opCode
  let header:=gateHeaderP.comp (opGateP.comp o)
  let wires:=wireWordsP.comp (cap.pair (opWiresP.comp o))
  exact (append.comp (header.pair wires)).congrFun (by intro x;rfl)
noncomputable def dataViewP : Procedure dataCode dataPayload dataView:=
  (identity dataPayload).precompose dataView
noncomputable def qubitsP : Procedure dataCode unaryCode Data.qubits:=
  (first unaryCode (listCode opCode)).comp dataViewP
noncomputable def opsP : Procedure dataCode (listCode opCode) Data.ops:=
  (second unaryCode (listCode opCode)).comp dataViewP
noncomputable def encodeClippedP : Procedure dataCode id Data.encodeClipped := by
  let qword:=natWordP.comp qubitsP
  let len:=(NativeAIG.Emission.listUnaryLength opCode ⟨plainGate .not,[]⟩).comp opsP
  let nword:=natWordP.comp len
  let words:=(listMapWith (f:=fun cap (o : Op)=>o.encodeClipped cap)
    ⟨plainGate .not,[]⟩ [] opEncodeClippedP).comp (qubitsP.pair opsP)
  let payload:=listJoinWords.comp words
  exact (append.comp ((append.comp (qword.pair nword)).pair payload)).congrFun (by intro x;rfl)
end Emission

end ExactQuantumFactoring.CircuitEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CircuitEmissionBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Procedure
namespace Emission
noncomputable def opPackP : Procedure opPayload opCode (fun x=>Op.mk x.1 x.2):=
  (identity opPayload).result (by intro x;rfl)
noncomputable def dataPackP : Procedure dataPayload dataCode (fun x=>Data.mk x.1 x.2):=
  (identity dataPayload).result (by intro x;rfl)
noncomputable def gatePackP : Procedure gatePayload gateCode (fun x=>Gate.mk x.1 x.2.1 x.2.2):=
  (identity gatePayload).result (by intro x;rfl)
noncomputable def gateReverseP : Procedure gateCode gateCode Gate.reverse:=
  gatePackP.comp (gatePrimitiveP.pair ((boolNot.comp gateInverseP).pair gateControlledP))
noncomputable def opReverseP : Procedure opCode opCode Op.reverse:=
  opPackP.comp ((gateReverseP.comp opGateP).pair opWiresP)
noncomputable def opsReverseP : Procedure (listCode opCode) (listCode opCode)
    (fun xs=>xs.reverse.map Op.reverse):=
  (listMap ⟨plainGate .not,[]⟩ ⟨plainGate .not,[]⟩ opReverseP).comp (listReverse opCode ⟨plainGate .not,[]⟩)
noncomputable def opMapWith {α : Type} {ea : α→List Bool} {f : α→ℕ→ℕ}
    (p : Procedure (prodCode ea Nat.bits) Nat.bits (fun x=>f x.1 x.2)) :
    Procedure (prodCode ea opCode) opCode (fun x=>x.2.map (f x.1)):=by
  let a:=first ea opCode
  let o:=second ea opCode
  exact opPackP.comp ((opGateP.comp o).pair (((listMapWith 0 0 p)).comp (a.pair (opWiresP.comp o))))
noncomputable def opsMapWith {α : Type} {ea : α→List Bool} {f : α→ℕ→ℕ}
    (p : Procedure (prodCode ea Nat.bits) Nat.bits (fun x=>f x.1 x.2)) :
    Procedure (prodCode ea (listCode opCode)) (listCode opCode) (fun x=>x.2.map (Op.map (f x.1))):=
  listMapWith (f:=fun (a : α) (o : Op)=>o.map (f a)) ⟨plainGate .not,[]⟩ ⟨plainGate .not,[]⟩ (opMapWith p)
noncomputable def opsAppendP : Procedure (prodCode (listCode opCode) (listCode opCode)) (listCode opCode)
    (fun x=>x.1++x.2):=listAppend opCode ⟨plainGate .not,[]⟩
noncomputable def notOpP : Procedure Nat.bits opCode notOp:=by
  let wires:=(listCons Nat.bits).comp ((identity Nat.bits).pair (Procedure.constant _ (listCode Nat.bits) []))
  exact opPackP.comp ((Procedure.constant Nat.bits gateCode (plainGate .not)).pair wires)
noncomputable def cnotOpP : Procedure (prodCode Nat.bits Nat.bits) opCode (fun x=>cnotOp x.1 x.2):=by
  let a:=first Nat.bits Nat.bits
  let b:=second Nat.bits Nat.bits
  let tail:=(listCons Nat.bits).comp (b.pair (Procedure.constant _ (listCode Nat.bits) []))
  let wires:=(listCons Nat.bits).comp (a.pair tail)
  exact opPackP.comp ((Procedure.constant _ gateCode (plainGate .cnot)).pair wires)
noncomputable def toffoliOpP : Procedure (prodCode Nat.bits (prodCode Nat.bits Nat.bits)) opCode
    (fun x=>toffoliOp x.1 x.2.1 x.2.2):=by
  let a:=first Nat.bits (prodCode Nat.bits Nat.bits)
  let rs:=second Nat.bits (prodCode Nat.bits Nat.bits)
  let b:=(first Nat.bits Nat.bits).comp rs
  let c:=(second Nat.bits Nat.bits).comp rs
  let tail:=(listCons Nat.bits).comp (c.pair (Procedure.constant _ (listCode Nat.bits) []))
  let mid:=(listCons Nat.bits).comp (b.pair tail)
  let wires:=(listCons Nat.bits).comp (a.pair mid)
  exact opPackP.comp ((Procedure.constant _ gateCode (plainGate .toffoli)).pair wires)
noncomputable def opSingletonP : Procedure opCode (listCode opCode) (fun o=>[o]):=
  (listCons opCode).comp ((identity opCode).pair (Procedure.constant opCode (listCode opCode) []))
noncomputable def nodeOpsP : Procedure (prodCode Nat.bits NetworkEmission.nodeCode) (listCode opCode)
    (fun x=>nodeOps x.1 x.2):=by
  let t:=first Nat.bits NetworkEmission.nodeCode
  let o:=second Nat.bits NetworkEmission.nodeCode
  let tag:=NetworkEmission.Emission.nodeTagP.comp o
  let eq (i : ℕ):=binaryEq.comp (tag.pair (Procedure.constant _ Nat.bits i))
  let a:=NetworkEmission.Emission.nodeLhsP.comp o
  let b:=NetworkEmission.Emission.nodeRhsP.comp o
  let n:=opSingletonP.comp (notOpP.comp t)
  let c:=opSingletonP.comp (cnotOpP.comp (a.pair t))
  let neg:=opsAppendP.comp (c.pair n)
  let conj:=conditional (binaryEq.comp (a.pair b)) c
    (opSingletonP.comp (toffoliOpP.comp (a.pair (b.pair t))))
  let const:=conditional (NetworkEmission.Emission.nodeBoolP.comp o) n (Procedure.constant _ (listCode opCode) [])
  exact (conditional (eq 0) const (conditional (eq 1) c (conditional (eq 2) neg conj))).congrFun (by
    rintro ⟨t,o⟩
    cases o with
    | constant b=>cases b <;> rfl
    | copy i=>rfl
    | neg i=>rfl
    | conj a b=>simp only [Function.comp_apply,NetworkEmission.nodeView,decide_eq_true_eq,nodeOps];rfl)
noncomputable def netOpsP : Procedure (prodCode Nat.bits (listCode NetworkEmission.nodeCode)) (listCode opCode)
    (fun x=>netOps x.1 x.2):=by
  let n:=first Nat.bits (prodCode Nat.bits NetworkEmission.nodeCode)
  let rs:=second Nat.bits (prodCode Nat.bits NetworkEmission.nodeCode)
  let i:=(first Nat.bits NetworkEmission.nodeCode).comp rs
  let o:=(second Nat.bits NetworkEmission.nodeCode).comp rs
  let step:=nodeOpsP.comp ((binaryAdd.comp (n.pair i)).pair o)
  let xs:=listMapIdxWith (f:=fun n i o=>nodeOps (n+i) o) (.constant false) [] step
  exact (listFlatten opCode ⟨plainGate .not,[]⟩).comp xs
noncomputable def copyOpsP : Procedure (prodCode Nat.bits (listCode Nat.bits)) (listCode opCode)
    (fun x=>copyOps x.1 x.2):=by
  let n:=first Nat.bits (prodCode Nat.bits Nat.bits)
  let rs:=second Nat.bits (prodCode Nat.bits Nat.bits)
  let i:=(first Nat.bits Nat.bits).comp rs
  let a:=(second Nat.bits Nat.bits).comp rs
  let step:=cnotOpP.comp (a.pair (binaryAdd.comp (n.pair i)))
  exact listMapIdxWith (f:=fun n i a=>cnotOp a (n+i)) 0 ⟨plainGate .not,[]⟩ step
noncomputable def oracleOpsP : Procedure NetworkEmission.dataCode (listCode opCode) oracleOps:=by
  let n:=NetworkEmission.Emission.dataInputP
  let xs:=NetworkEmission.Emission.dataNodesP
  let os:=NetworkEmission.Emission.dataOutputsP
  let w:=NetworkEmission.Emission.dataWidthP
  let p:=netOpsP.comp (n.pair xs)
  exact opsAppendP.comp ((opsAppendP.comp (p.pair (copyOpsP.comp (w.pair os)))).pair (opsReverseP.comp p))
end Emission
end ExactQuantumFactoring.CircuitEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkEmissionWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
def borPack (a b : Pack) : Pack:=bnotPack (bandPack (bnotPack a) (bnotPack b))
def muxPack (c a b : Pack) : Pack:=borPack (bandPack c a) (bandPack (bnotPack c) b)

def wordConstPack (n w c : ℕ) : Pack:=vectorPack n ((List.range w).map (fun i=>constantPack n (c.testBit i)))

def wordMuxPack (w : ℕ) (c a b : Pack) : Pack:=
  compPack (pairPack (pairPack c a) b) (vectorPack (1+w+w) ((List.range w).map (fun i=>
    muxPack (bitPack (1+w+w) 0) (bitPack (1+w+w) (1+i)) (bitPack (1+w+w) (1+w+i)))))
namespace Emission
noncomputable def borPackP : Procedure (prodCode packCode packCode) packCode (fun x=>borPack x.1 x.2):=
  bnotPackP.comp (bandPackP.comp (bnotPackP.parallel bnotPackP))
noncomputable def muxPackP : Procedure (prodCode packCode (prodCode packCode packCode)) packCode
    (fun x=>muxPack x.1 x.2.1 x.2.2):=by
  let c:=first packCode (prodCode packCode packCode)
  let a:=(first packCode packCode).comp (second packCode (prodCode packCode packCode))
  let b:=(second packCode packCode).comp (second packCode (prodCode packCode packCode))
  exact borPackP.comp ((bandPackP.comp (c.pair a)).pair (bandPackP.comp ((bnotPackP.comp c).pair b)))
noncomputable def wordConstPackP : Procedure (prodCode unaryCode (prodCode unaryCode Nat.bits)) packCode
    (fun x=>wordConstPack x.1 x.2.1 x.2.2):=by
  let idx:=first unaryCode (prodCode unaryCode Nat.bits)
  let e:=second unaryCode (prodCode unaryCode Nat.bits)
  let n:=(first unaryCode Nat.bits).comp e
  let c:=(second unaryCode Nat.bits).comp e
  let step:=constantPackP.comp (n.pair (testBit.comp (c.pair idx)))
  let n₀:=first unaryCode (prodCode unaryCode Nat.bits)
  let rest:=second unaryCode (prodCode unaryCode Nat.bits)
  let c₀:=(second unaryCode Nat.bits).comp rest
  let w₀:=(first unaryCode Nat.bits).comp rest
  let parts:=(tabulate (f:=fun (x:ℕ×ℕ) i=>constantPack x.1 (x.2.testBit i)) emptyPack step).comp (w₀.pair (n₀.pair c₀))
  exact vectorPackP.comp (n₀.pair parts)
noncomputable def muxVectorPackP : Procedure unaryCode packCode
    (fun w=>vectorPack (1+w+w) ((List.range w).map (fun i=>muxPack (bitPack (1+w+w) 0)
      (bitPack (1+w+w) (1+i)) (bitPack (1+w+w) (1+w+i))))):=by
  let i:=unaryToBits.comp (first unaryCode unaryCode)
  let w:=second unaryCode unaryCode
  let width:=unarySuccessor.comp (unaryAdd.comp (w.pair w))
  let c:=bitPackP.comp (width.pair (Procedure.constant _ Nat.bits 0))
  let a:=bitPackP.comp (width.pair (successor.comp i))
  let b:=bitPackP.comp (width.pair (successor.comp (binaryAdd.comp ((unaryToBits.comp w).pair i))))
  let step:=muxPackP.comp (c.pair (a.pair b))
  let parts:=(tabulate (f:=fun w i=>muxPack (bitPack (1+w+w) 0) (bitPack (1+w+w) (1+i))
    (bitPack (1+w+w) (1+w+i))) emptyPack (step.congrFun (by intro x;simp only [Function.comp_apply,id_eq,Nat.succ_eq_add_one]; simp only [Nat.add_assoc,Nat.add_comm]))).comp
    ((identity unaryCode).pair (identity unaryCode))
  let width₀:=unarySuccessor.comp (unaryAdd.comp ((identity unaryCode).pair (identity unaryCode)))
  exact (vectorPackP.comp (width₀.pair parts)).congrFun (by intro w;simp only [Function.comp_apply,id_eq,Nat.succ_eq_add_one]; simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm])
noncomputable def wordMuxPackP : Procedure (prodCode unaryCode (prodCode packCode (prodCode packCode packCode))) packCode
    (fun x=>wordMuxPack x.1 x.2.1 x.2.2.1 x.2.2.2):=by
  let rest:=second unaryCode (prodCode packCode (prodCode packCode packCode))
  let c:=(first packCode (prodCode packCode packCode)).comp rest
  let ab:=(second packCode (prodCode packCode packCode)).comp rest
  let a:=(first packCode packCode).comp ab
  let b:=(second packCode packCode).comp ab
  exact compPackP.comp ((pairPackP.comp ((pairPackP.comp (c.pair a)).pair b)).pair
    (muxVectorPackP.comp (first unaryCode (prodCode packCode (prodCode packCode packCode)))))
end Emission
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkStackCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
def stackStep (o : StackOp) (s : List Pack) : List Pack:=match o with
  | .inl a=>a::s
  | .inr b=>let a:=s.tail.headD emptyPack;let c:=s.headD emptyPack
    (if b then compPack a c else pairPack a c)::s.tail.tail
def opWeight : StackOp→ℕ | .inl a=>a.val.budget | .inr _=>0
lemma stackStep_budget (o : StackOp) (s : List Pack) :
    stackBudget (stackStep o s)≤ stackBudget s+opWeight o:=by
  cases o with
  | inl a=>simp [stackStep,stackBudget,opWeight,Nat.add_comm]
  | inr b=>
    cases s with
    | nil=>cases b <;> simp [stackStep,stackBudget,opWeight,emptyPack,selectPack,pairPack,compPack]
    | cons a s=>cases s with
      | nil=>cases b <;> simp [stackStep,stackBudget,opWeight,emptyPack,selectPack,pairPack,compPack]
      | cons c s=>cases b <;> simp [stackStep,stackBudget,opWeight,pairPack,compPack,Nat.add_comm,Nat.add_assoc]
lemma stackStep_length (o : StackOp) (s : List Pack) : (stackStep o s).length≤ s.length+1:=by
  cases o <;> simp [stackStep,List.length_tail];omega
lemma stackFold_budget (ops : List StackOp) (s : List Pack) :
    stackBudget (ops.foldl (fun s o=>stackStep o s) s)≤ stackBudget s+(ops.map opWeight).sum:=by
  induction ops generalizing s with
  | nil=>simp
  | cons o ops ih=>
    have hs:=stackStep_budget o s
    have hh:=ih (stackStep o s)
    simp only [List.foldl_cons,List.map_cons,List.sum_cons]
    omega
lemma stackFold_length (ops : List StackOp) (s : List Pack) :
    (ops.foldl (fun s o=>stackStep o s) s).length≤ s.length+ops.length:=by
  induction ops generalizing s with
  | nil=>simp
  | cons o ops ih=>
    have hs:=stackStep_length o s
    have hh:=ih (stackStep o s)
    simp only [List.foldl_cons,List.length_cons];omega
lemma opWeight_le_code (o : StackOp) : opWeight o≤(stackOpCode o).length:=by
  cases o with
  | inl a=>have h:=packBudget_le_code a;simp only [stackOpCode,sumCode,List.length_cons,opWeight];omega
  | inr b=>simp [opWeight]
lemma opWeights_le_code (ops : List StackOp) : (ops.map opWeight).sum≤(listCode stackOpCode ops).length:=by
  induction ops with
  | nil=>simp
  | cons o ops ih=>
    have hh:=opWeight_le_code o
    simp only [List.map_cons,List.sum_cons,listCode_length_cons];omega
lemma stackCode_bound (s : List Pack) :
    (listCode packCode s).length≤ s.length*(208*(stackBudget s+1)^2+2)+1:=by
  have hh:=listCode_length_bound packCode s (104*(stackBudget s+1)^2) (by
    intro a ha
    have hb : a.val.budget≤ stackBudget s:=List.single_le_sum (fun _ _=>Nat.zero_le _) _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
    exact (packCode_bound a).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)))
  convert hh using 1 <;> first | rfl | ring

end ExactQuantumFactoring.NetworkEmission
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
open BitStackProgram BitStackProgram.Procedure
open AIGNetworkEmission

def primPack (w : ℕ) : ℕ→Pack
  | 0=>binaryPack NativeAIG.add w
  | 1=>binaryPack NativeAIG.mul w
  | 2=>binaryPack NativeAIG.sub w
  | 3=>binaryPack NativeAIG.divide w
  | 4=>binaryPack NativeAIG.remainder w
  | 5=>ultPack w
  | 6=>nodePack 1 (.neg 0) (by simp [Node.Bound])
  | _=>vectorPack (1+w+w) ((List.range w).map (fun i=>muxPack (bitPack (1+w+w) 0)
      (bitPack (1+w+w) (1+i)) (bitPack (1+w+w) (1+w+i))))
def tokenOp {v : Type} (n w : ℕ) (vars : v→Pack) : ExprToken v→StackOp
  | .inl i=>.inl (vars i)
  | .inr (.inl c)=>.inl (wordConstPack n w c)
  | .inr (.inr 0)=>.inr false
  | .inr (.inr 1)=>.inr true
  | .inr (.inr (j+2))=>.inl (primPack w j)
def exprRun {v : Type} (n w : ℕ) (vars : v→Pack) (ts : List (ExprToken v)) (s : List Pack) : List Pack:=
  (ts.map (tokenOp n w vars)).foldl (fun s o=>stackStep o s) s
lemma exprRun_append {v : Type} (n w : ℕ) (vars : v→Pack) (ts us : List (ExprToken v)) (s : List Pack) :
    exprRun n w vars (ts++us) s=exprRun n w vars us (exprRun n w vars ts s):=by
  simp only [exprRun,List.map_append,List.foldl_append]
def Produces {v : Type} (n w : ℕ) (vars : v→Pack) (ts : List (ExprToken v)) (p : Pack) : Prop:=
  ∀s,exprRun n w vars ts s=p::s
lemma produces_var {v : Type} (n w : ℕ) (vars : v→Pack) (i : v) : Produces n w vars [.inl i] (vars i):=by
  intro s;rfl
lemma produces_const {v : Type} (n w : ℕ) (vars : v→Pack) (c : ℕ) :
    Produces n w vars [.inr (.inl c)] (wordConstPack n w c):=by intro s;rfl
lemma produces_op {v : Type} {n w : ℕ} {vars : v→Pack} {ts : List (ExprToken v)} {a : Pack}
    (ha : Produces n w vars ts a) (j : ℕ) :
    Produces n w vars (ts++[opToken j,compToken]) (compPack a (primPack w j)):=by
  intro s;rw [exprRun_append,ha];rfl
lemma produces_pair {v : Type} {n w : ℕ} {vars : v→Pack} {ts us : List (ExprToken v)} {a b : Pack}
    (ha : Produces n w vars ts a) (hb : Produces n w vars us b) :
    Produces n w vars (ts++us++[pairToken]) (pairPack a b):=by
  intro s;rw [exprRun_append,exprRun_append,ha,hb];rfl
lemma produces_binary {v : Type} {n w : ℕ} {vars : v→Pack} {ts us : List (ExprToken v)} {a b : Pack}
    (ha : Produces n w vars ts a) (hb : Produces n w vars us b) (j : ℕ) :
    Produces n w vars ((ts++us++[pairToken])++[opToken j,compToken]) (compPack (pairPack a b) (primPack w j)):=
  produces_op (produces_pair ha hb) j

def lePack (w : ℕ) (a b : Pack) : Pack:=bnotPack (compPack (pairPack b a) (ultPack w))
lemma produces_le {v : Type} {n w : ℕ} {vars : v→Pack} {ts us : List (ExprToken v)} {a b : Pack}
    (ha : Produces n w vars ts a) (hb : Produces n w vars us b) :
    Produces n w vars (leTokens ts us) (lePack w a b):=
  produces_op (produces_binary hb ha 5) 6
lemma produces_mux {v : Type} {n w : ℕ} {vars : v→Pack} {ts us vs : List (ExprToken v)} {c a b : Pack}
    (hc : Produces n w vars ts c) (ha : Produces n w vars us a) (hb : Produces n w vars vs b) :
    Produces n w vars (muxTokens ts us vs) (wordMuxPack w c a b):=
  produces_op (produces_pair (produces_pair hc ha) hb) 7

def exprPack {v : Type} (n w : ℕ) (vars : v→Pack) : NatExpr v→Pack
  | .var i=>vars i
  | .const c=>wordConstPack n w c
  | .add a b=>compPack (pairPack (exprPack n w vars a) (exprPack n w vars b)) (binaryPack NativeAIG.add w)
  | .mul a b=>compPack (pairPack (exprPack n w vars a) (exprPack n w vars b)) (binaryPack NativeAIG.mul w)
  | .sub a b=>wordMuxPack w (lePack w (exprPack n w vars b) (exprPack n w vars a))
      (compPack (pairPack (exprPack n w vars a) (exprPack n w vars b)) (binaryPack NativeAIG.sub w)) (wordConstPack n w 0)
  | .div a b=>compPack (pairPack (exprPack n w vars a) (exprPack n w vars b)) (binaryPack NativeAIG.divide w)
  | .mod a b=>compPack (pairPack (exprPack n w vars a) (exprPack n w vars b)) (binaryPack NativeAIG.remainder w)
  | .iteLe a b c d=>wordMuxPack w (lePack w (exprPack n w vars a) (exprPack n w vars b))
      (exprPack n w vars c) (exprPack n w vars d)
lemma exprTokens_produces {v : Type} (n w : ℕ) (vars : v→Pack) (e : NatExpr v) :
    Produces n w vars (exprTokens e) (exprPack n w vars e):=by
  induction e with
  | var i=>exact produces_var n w vars i
  | const c=>exact produces_const n w vars c
  | add a b ha hb=>exact produces_binary ha hb 0
  | mul a b ha hb=>exact produces_binary ha hb 1
  | div a b ha hb=>exact produces_binary ha hb 3
  | mod a b ha hb=>exact produces_binary ha hb 4
  | sub a b ha hb=>exact produces_mux (produces_le hb ha) (produces_binary ha hb 2) (produces_const n w vars 0)
  | iteLe a b c d ha hb hc hd=>exact produces_mux (produces_le ha hb) hc hd
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_EmissionFurther
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

namespace Emission
noncomputable def combineStackP : Procedure (prodCode boolCode (listCode packCode)) (listCode packCode)
    (fun x=>stackStep (.inr x.1) x.2):=by
  let sw:=first boolCode (listCode packCode)
  let s:=second boolCode (listCode packCode)
  let tl:=(listTail (ea:=packCode)).comp s
  let a:=(listHead packCode emptyPack).comp tl
  let b:=(listHead packCode emptyPack).comp s
  let o:=conditional sw (compPackP.comp (a.pair b)) (pairPackP.comp (a.pair b))
  exact ((listCons packCode).comp (o.pair ((listTail (ea:=packCode)).comp tl))).congrFun (by intro x;rfl)
noncomputable def stackStepP : Procedure (prodCode stackOpCode (listCode packCode)) (listCode packCode)
    (fun x=>stackStep x.1 x.2):=by
  let o:=first stackOpCode (listCode packCode)
  let s:=second stackOpCode (listCode packCode)
  let tag:=(casesSum (Procedure.constant packCode boolCode false) (Procedure.constant boolCode boolCode true)).comp o
  let p:=(casesSum (identity packCode) (Procedure.constant boolCode packCode emptyPack)).comp o
  let b:=(casesSum (Procedure.constant packCode boolCode false) (identity boolCode)).comp o
  exact (conditional tag (combineStackP.comp (b.pair s)) ((listCons packCode).comp (p.pair s))).congrFun (by
    rintro ⟨o,s⟩;cases o <;> rfl)
noncomputable def stackFoldP : Procedure (prodCode (listCode stackOpCode) (listCode packCode)) (listCode packCode)
    (fun x=>x.1.foldl (fun s o=>stackStep o s) x.2):=
  foldList (.inr false) stackStepP (Polynomial.X*(Polynomial.C 208*(Polynomial.X+1)^2+2)+1) (by
    intro ops s i
    let t:=(ops.take i).foldl (fun s o=>stackStep o s) s
    have hb:=stackFold_budget (ops.take i) s
    have hs:=packBudgets_le_code s
    have ho:=(opWeights_le_code (ops.take i)).trans (listCode_length_take_le stackOpCode i ops)
    have hlen:=stackFold_length (ops.take i) s
    have hop:=(list_length_le_code stackOpCode (ops.take i)).trans (listCode_length_take_le stackOpCode i ops)
    have hss:=list_length_le_code packCode s
    have hB : stackBudget t+1≤(listCode stackOpCode ops).length+(listCode packCode s).length+1:=by
      change stackBudget s≤_ at hs
      dsimp only [t];omega
    have hL : t.length≤(listCode stackOpCode ops).length+(listCode packCode s).length:=by dsimp only [t];omega
    have hh:=stackCode_bound t
    have hm:=Nat.mul_le_mul hL (Nat.add_le_add_right (Nat.mul_le_mul_left 208 (Nat.pow_le_pow_left hB 2)) 2)
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      Polynomial.eval_pow,Polynomial.eval_one,Polynomial.eval_ofNat]
    exact hh.trans (Nat.add_le_add_right hm 1))
end Emission
end ExactQuantumFactoring.NetworkEmission

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
open BitStackProgram BitStackProgram.Procedure AIGNetworkEmission
namespace Emission
noncomputable def primPackP : Procedure (prodCode unaryCode Nat.bits) packCode (fun x=>primPack x.1 x.2):=by
  let w:=first unaryCode Nat.bits
  let j:=second unaryCode Nat.bits
  let eq (i:ℕ):=binaryEq.comp (j.pair (Procedure.constant _ Nat.bits i))
  let a:=AIGNetworkEmission.Emission.addPackP.comp w
  let b:=AIGNetworkEmission.Emission.mulPackP.comp w
  let c:=AIGNetworkEmission.Emission.subPackP.comp w
  let d:=AIGNetworkEmission.Emission.divPackP.comp w
  let e:=AIGNetworkEmission.Emission.modPackP.comp w
  let f:=AIGNetworkEmission.Emission.ultPackP.comp w
  let g:=Procedure.constant (prodCode unaryCode Nat.bits) packCode (nodePack 1 (.neg 0) (by simp [Node.Bound]))
  let h:=muxVectorPackP.comp w
  exact (conditional (eq 0) a (conditional (eq 1) b (conditional (eq 2) c (conditional (eq 3) d
    (conditional (eq 4) e (conditional (eq 5) f (conditional (eq 6) g h))))))).congrFun (by
    rintro ⟨w,j⟩
    rcases j with _|j <;> simp only [Function.comp_apply,decide_eq_true_eq,primPack]
    · rfl
    rcases j with _|j
    · rfl
    rcases j with _|j
    · rfl
    rcases j with _|j
    · rfl
    rcases j with _|j
    · rfl
    rcases j with _|j
    · rfl
    rcases j with _|j
    · rfl
    simp)

def envVars (xs : List Pack) (i : ℕ) : Pack:=(xs.drop i).headD emptyPack
noncomputable def tokenOpP : Procedure (prodCode exprEnvCode (exprTokenCode Nat.bits)) stackOpCode
    (fun x=>tokenOp x.1.1 x.1.2.1 (envVars x.1.2.2) x.2):=by
  let env:=first exprEnvCode (exprTokenCode Nat.bits)
  let n:=(first unaryCode (prodCode unaryCode (listCode packCode))).comp env
  let rest:=(second unaryCode (prodCode unaryCode (listCode packCode))).comp env
  let w:=(first unaryCode (listCode packCode)).comp rest
  let vs:=(second unaryCode (listCode packCode)).comp rest
  let tok:=second exprEnvCode (exprTokenCode Nat.bits)
  let tag:=tokenTagP.comp tok
  let val:=tokenPayloadP.comp tok
  let eq (i:ℕ) (p:Procedure (prodCode exprEnvCode (exprTokenCode Nat.bits)) Nat.bits (fun x=>i)):=
    binaryEq.comp (tag.pair p)
  let v:=(sumLeft packCode boolCode).comp ((listGet packCode emptyPack).comp (val.pair vs))
  let c:=(sumLeft packCode boolCode).comp (wordConstPackP.comp (n.pair (w.pair val)))
  let op:=(sumLeft packCode boolCode).comp (primPackP.comp (w.pair (binarySub.comp (val.pair (Procedure.constant _ Nat.bits 2)))))
  let inst:=conditional (binaryEq.comp (val.pair (Procedure.constant _ Nat.bits 0)))
    (Procedure.constant _ stackOpCode (.inr false))
    (conditional (binaryEq.comp (val.pair (Procedure.constant _ Nat.bits 1))) (Procedure.constant _ stackOpCode (.inr true)) op)
  exact (conditional (eq 0 (Procedure.constant _ Nat.bits 0)) v
    (conditional (eq 1 (Procedure.constant _ Nat.bits 1)) c inst)).congrFun (by
      rintro ⟨⟨n,w,vs⟩,t⟩
      rcases t with i|c|j
      · rfl
      · rfl
      rcases j with _|j
      · rfl
      rcases j with _|j
      · rfl
      simp only [Function.comp_apply,tokenTag,tokenPayload,tokenOp,decide_eq_true_eq,
        Nat.add_one_ne_zero,↓reduceIte]
      rfl)
noncomputable def exprRunP : Procedure (prodCode exprEnvCode (listCode (exprTokenCode Nat.bits))) (listCode packCode)
    (fun x=>exprRun x.1.1 x.1.2.1 (envVars x.1.2.2) x.2 []):=by
  let ops:=listMapWith (f:=fun (env : ExprEnv) t=>tokenOp env.1 env.2.1 (envVars env.2.2) t) (Sum.inl 0) (Sum.inr false) tokenOpP
  let start:=(ops.pair (Procedure.constant _ (listCode packCode) []))
  exact stackFoldP.comp start
noncomputable def exprResultP : Procedure (prodCode exprEnvCode (listCode (exprTokenCode Nat.bits))) packCode
    (fun x=>(exprRun x.1.1 x.1.2.1 (envVars x.1.2.2) x.2 []).headD emptyPack):=
  (listHead packCode emptyPack).comp exprRunP
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
open BitStackProgram BitStackProgram.Procedure BitStackProgram.Emits
variable {v : Type}
lemma tokenMap_op (f : v→ℕ) (n w : ℕ) (vs : ℕ→Pack) (t : ExprToken v) :
    tokenOp n w vs (tokenMap f t)=tokenOp n w (fun i=>vs (f i)) t:=by
  rcases t with i|c|j
  · rfl
  · rfl
  · rcases j with _|j <;> try rfl
    rcases j with _|j <;> rfl
lemma tokenMap_run (f : v→ℕ) (n w : ℕ) (vs : ℕ→Pack) (ts : List (ExprToken v)) (s : List Pack) :
    exprRun n w vs (ts.map (tokenMap f)) s=exprRun n w (fun i=>vs (f i)) ts s:=by
  simp only [exprRun,List.map_map,Function.comp_def,tokenMap_op]
namespace Emission
noncomputable def genericExprResultP (f : v→ℕ) : Procedure
    (prodCode exprEnvCode (listCode (exprTokenCode (fun i=>(f i).bits)))) packCode
    (fun x=>(exprRun x.1.1 x.1.2.1 (fun i=>envVars x.1.2.2 (f i)) x.2 []).headD emptyPack):=by
  let p:=exprResultP.precompose (fun x : ExprEnv×List (ExprToken v)=>(x.1,x.2.map (tokenMap f)))
  exact (p.congrEncoding (by intro x;dsimp only [prodCode];rw [tokenMap_listCode]) (by intro x;rfl)).congrFun (by
    intro x;dsimp only [Function.comp_apply];rw [tokenMap_run])
noncomputable def genericExprPackP (f : v→ℕ) : Procedure
    (prodCode exprEnvCode (exprCode (fun i=>(f i).bits))) packCode
    (fun x=>exprPack x.1.1 x.1.2.1 (fun i=>envVars x.1.2.2 (f i)) x.2):=
  ((genericExprResultP f).comp ((first _ _).pair ((exprTokensP _).comp (second _ _)))).congrFun (by
    intro x;change (exprRun _ _ _ (exprTokens x.2) []).headD emptyPack=_
    rw [exprTokens_produces];rfl)
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkResizeEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

def resizePack (u w : ℕ) : Pack:=vectorPack u ((List.range w).map
  (fun i=>if i<u then bitPack u i else constantPack u false))
namespace Emission
noncomputable def resizePackP : Procedure (prodCode unaryCode unaryCode) packCode (fun x=>resizePack x.1 x.2):=by
  let i:=unaryToBits.comp (first unaryCode unaryCode)
  let u:=second unaryCode unaryCode
  let test:=binaryLt.comp (i.pair (unaryToBits.comp u))
  let step:=conditional test (bitPackP.comp (u.pair i))
    (constantPackP.comp (u.pair (Procedure.constant _ boolCode false)))
  let step' : Procedure (prodCode unaryCode unaryCode) packCode
      (fun x=>if x.1<x.2 then bitPack x.2 x.1 else constantPack x.2 false):=
    step.congrFun (by intro x;simp only [Function.comp_apply,decide_eq_true_eq,id_eq])
  let xs:=(tabulate (f:=fun u i=>if i<u then bitPack u i else constantPack u false) emptyPack step').comp ((second unaryCode unaryCode).pair (first unaryCode unaryCode))
  exact vectorPackP.comp ((first unaryCode unaryCode).pair xs)
noncomputable def exprWidthP {vars : Type} (ev : vars→List Bool) : Procedure (prodCode unaryCode (exprCode ev)) unaryCode
    (fun x=>x.2.templateWidth x.1):=by
  let b:=first unaryCode (exprCode ev)
  let e:=second unaryCode (exprCode ev)
  let sz:=(exprSizeP ev).comp e
  let mc:=(exprMaxP ev).comp e
  let sizeP : Procedure Nat.bits unaryCode Nat.size:=
    (Procedure.length.precompose Nat.bits).congrFun (by intro n;exact n.size_eq_bits_len)
  let bitlen:=sizeP.comp mc
  exact unaryMul.comp ((unarySuccessor.comp (unaryAdd.comp (b.pair bitlen))).pair sz)
end Emission
end ExactQuantumFactoring.NetworkEmission

end


end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeInitialization
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
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

/-- Literal clean initialization: retain the runtime controller word and create
only zero history/output/scratch fields. No query result is precomputed. -/
def initialNet : (t : ℕ) → BooleanNetwork c (M.width t)
  | 0 => select id
  | t+1 => packNet M.updateWork
      (packNet M.initWork (initialNet t) (Completion.zeros c (NodeKernel.width n)))
      (Completion.zeros c c)

end NodeMachine
end ExactQuantumFactoring


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

def startNet (n : ℕ) : BooleanNetwork n (configWidth n) :=
  stackPush (select id) (Completion.zeros n (configWidth n))
abbrev width (n : ℕ) := (machine n).width (steps n)
def initialNet (n : ℕ) : BooleanNetwork n (width n) :=
  (startNet n).comp ((machine n).initialNet (steps n))

/-- Actual root readout from earlier retained wires, not a factor-table lookup. -/
def rootResult (n t : ℕ) : BooleanNetwork ((machine n).width (t+1)) (tensorWidth n n) :=
  ((machine n).firstNodeNet t).comp (nodeResult n)

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_HardFilterCircuit
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
namespace UniversalSplit

def hardOn {k n : ℕ} (m : BooleanNetwork k n) : BooleanNetwork k 1 :=
  ((wordLe (wordConstant (BitVec.ofNat n 2)) m).band (m.comp (primeWord n)).bnot).band
    ((evenOn m).bnot.band ((m.comp (resizeWord n (rootWidth n))).comp (perfectPowerNet n)).bnot)

end UniversalSplit
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetrospectiveLists
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
open AuxiliaryTree OrderTrial

noncomputable def dataGoodList (data : FactorData) (m n : ℕ)
    (y : Basis (Completion.transitionWidth n)) : Prop :=
  ∃ i : Fin (n^5),dataResidueGood data (bitsValue (TransitionWords.read y i)).toNat m

/-- A direct fixed-field validator: read field zero, test its supplied-factor CRT
congruences, and check every other field and the unused word is zero. -/
noncomputable def dataCanonicalList (data : FactorData) (m n : ℕ) (hn : 0<n)
    (y : Basis (Completion.transitionWidth n)) : Prop :=
  let a := TransitionWords.read y ⟨0,pow_pos hn 5⟩
  dataCanonicalResidue data (bitsValue a).toNat m ∧
    y=TransitionWords.encode (fun i : Fin (n^5) => if i.val=0 then a else natBasis n 0)

namespace Completion
/-- Equivalent form of dyadic completion for a retrospective, data-based test
of the guessed string. No canonical output is used during preparation. -/
def test {α : Type*} {W t d : ℕ} (good : α→Prop) (guessGood : Basis W→Prop)
    (s z : ℚ) (r : Raw α W t d) : Prop :=
  ordinaryPass good s z r ∨ rare r.1 ∧ guessGood r.2.2.1 ∧
    threshold (guessRetention W t s z) r.2.2.2
end Completion

noncomputable def dataListPassed {n : ℕ} (data : FactorData) (m : Basis n) (hn : 0<n)
    (r : PhysicalListSlots.Result n) : Prop :=
  Completion.test (fun x => dataGoodList data (bitsValue m).toNat n (PhysicalListSlots.ordinary x))
    (dataCanonicalList data (bitsValue m).toNat n hn)
    (dataListSuccess data (bitsValue m).toNat n (n^5)) (Completion.target n) r

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CompletionPredicateCircuit
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

/-- A deferred guess predicate, rather than a circuit that constructs the
canonical CRT string.  Both branches use the same retained completion coin. -/
def predicateFilter {v : Type*} {k b W t : ℕ} (d : ℕ)
    (s z : RatExpr v) (vars : v→BooleanNetwork k b)
    (branch : BooleanNetwork k t) (coin : NatExpr v)
    (good guessGood : BooleanNetwork k 1) : BooleanNetwork k 1 :=
  let rare:=zeroWord branch
  let ordinaryKeep:=retentionNet (coinBits W t d) (Expressions.coefficient W t s z) coin vars
  let guessKeep:=retentionNet (coinBits W t d) (Expressions.guess W t s z) coin vars
  ((rare.bnot).band (good.band ordinaryKeep)).bor
    (rare.band (guessGood.band guessKeep))

end Completion
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
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)
abbrev rowBound := M.query.net.count+97*n+25+
  factorVerifierBound n (M.query.net.count+PhysicalNode.resultBound n)
end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FlatLookupCircuit
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

namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

/-- The rows are at their true retained locations. This construction has no
quantum conditioning and does not evaluate a factorization operation. -/
def logNets : (t : ℕ)→List (BooleanNetwork (M.width t) n ×
    BooleanNetwork (M.width t) (tensorWidth n n))
  | 0=>[]
  | t+1=>(M.rowQuery t,(M.lastNodeNet t).comp (PhysicalTree.nodeResult n))::
      ((logNets t).map (fun r=>((M.previousNet t).comp r.1,(M.previousNet t).comp r.2)))

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TableOrderCircuit
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

/-- A zero/unused-row word is replaced by the harmless prime 2. -/
def tableFactor {k n : ℕ} (label p : BooleanNetwork k n) : BooleanNetwork k n :=
  wordMux ((zeroWord label).bor (zeroWord p)) (wordConstant 2) p

def tableNets {k n : ℕ} (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) :
    List (BooleanNetwork k n) := rows.flatMap (fun r=>r.2.map (tableFactor r.1))

def tableValues {k n : ℕ} (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) (x : Basis k) :
    List (ℕ×List ℕ) := rows.map (fun r=>((bitsValue (r.1.eval x)).toNat,
      r.2.map (fun p=>(bitsValue (p.eval x)).toNat)))

/-- Start at the complete product of a known prime list and scan it once.
This is sufficient whenever the group order divides that product. -/
def orderFromList {k w : ℕ} (a m : BooleanNetwork k w) (qs : List (BooleanNetwork k w)) :
    BooleanNetwork k w :=
  (((select id).pair (productNet qs)).comp (stripScan a m qs)).comp (select (Fin.natAdd k))

end BitArithmetic
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

def tableOrderPrimes {k n : ℕ}
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) :
    List (BooleanNetwork k (tableOrderWidth n (tableNets rows).length)) :=
  List.flatten (List.replicate n ((tableNets rows).map (fun p=>
    p.comp (resizeWord n (tableOrderWidth n (tableNets rows).length)))))

/-- A literal order circuit using only retained verified table entries and
modular powering. No mathematical factorization/support enumeration appears in
its definition, even on malformed inputs. -/
def tableOrder {k n : ℕ} (a m : BooleanNetwork k n)
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) : BooleanNetwork k n :=
  let w:=tableOrderWidth n (tableNets rows).length
  (orderFromList (a.comp (resizeWord n w)) (m.comp (resizeWord n w))
    (tableOrderPrimes rows)).comp (resizeWord w n)

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedTable
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
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

/-- Every field is selected from its actual retained location. Dummy rows
are kept: the rectangular shape is a compile-time function only of n and t. -/
def fieldRows (t : ℕ) : List (BooleanNetwork (M.width t) n ×
    List (BooleanNetwork (M.width t) n)) :=
  (M.logNets t).map (fun r=>(r.1,List.ofFn (fun i : Fin n=>r.2.comp (tensorSelect n n i))))

/-- The literal order network already available at any retained stage, before
adding its reversible phase-flag wrapper. -/
def retainedOrder (t : ℕ) (a m : BooleanNetwork (M.width t) n) : BooleanNetwork (M.width t) n :=
  tableOrder a m (M.fieldRows t)

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedCanonical
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
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

def retainedCanonical (t : ℕ) (a m : BooleanNetwork (M.width t) n) : BooleanNetwork (M.width t) 1 :=
  tableCanonicalNet (tableNets (M.fieldRows t)) a m

end NodeMachine

namespace TransitionWords

def readNet {k n K : ℕ} (y : BooleanNetwork k (n*(K+1))) (i : Fin K) : BooleanNetwork k n :=
  y.rewire (fun j=>Fin.cast (Nat.mul_comm _ _) (finProdFinEquiv (i.castSucc,j)))

/-- A polynomial-size literal shape check, including the otherwise-unused last
word. It does not construct the unknown canonical CRT residue. -/
def firstOnly {k n K : ℕ} (a : BooleanNetwork k n) : BooleanNetwork k (n*(K+1)) :=
  encodeNet (fun i : Fin K=>if i.val=0 then a else wordConstant (BitVec.ofNat n 0))
end TransitionWords

namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

def retainedCanonicalList (hn : 0<n) (t : ℕ) (m : BooleanNetwork (M.width t) n)
    (y : BooleanNetwork (M.width t) (n*(n^5+1))) : BooleanNetwork (M.width t) 1 :=
  let a:=TransitionWords.readNet y ⟨0,pow_pos hn 5⟩
  (M.retainedCanonical t a m).band (equalOn y (TransitionWords.firstOnly a))

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedComponentOrder
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
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

def retainedComponentOrder (t : ℕ) (a m p : BooleanNetwork (M.width t) n) : BooleanNetwork (M.width t) n :=
  M.retainedOrder t a (primeComponent m p)

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TwoAdicCircuit
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

/-- Equality of exact dyadic valuations by bounded divisibility tests.  The
parameter is the word width, not an input-dependent search cap. -/
def sameTwoVal {k n : ℕ} (a b : BooleanNetwork k n) : BooleanNetwork k 1 :=
  all (List.ofFn (fun i : Fin n=>bequiv (a.comp (dividesNet n (2^i.val)))
    (b.comp (dividesNet n (2^i.val)))))

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedFavorable
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
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

/-- All component computations read the same retained, verified occurrence log.
Only primes dividing the requested cofactor contribute to the comparison. -/
def retainedFavorable (t : ℕ) (a m : BooleanNetwork (M.width t) n) : BooleanNetwork (M.width t) 1 :=
  let ps:=tableNets (M.fieldRows t)
  (OrderSlots.usableOn a m).band ((all (ps.map (fun p=>all (ps.map (fun q=>
    (dividesOn p m).bnot.bor ((dividesOn q m).bnot.bor
      (sameTwoVal (M.retainedComponentOrder t a m p) (M.retainedComponentOrder t a m q)))))))).bnot)

def retainedGoodList (t : ℕ) (m : BooleanNetwork (M.width t) n)
    (y : BooleanNetwork (M.width t) (n*(n^5+1))) : BooleanNetwork (M.width t) 1 :=
  any (List.ofFn (fun i : Fin (n^5)=>M.retainedFavorable t (TransitionWords.readNet y i) m))

end NodeMachine
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

/-- A division-based totient step. Redundant prime entries do nothing. -/
def totientPair {k w : ℕ} (q v a : BooleanNetwork k w) : BooleanNetwork k (w+w) :=
  let d := (v.pair q).comp (div w)
  let cond := zeroWord ((v.pair q).comp (mod w))
  let weight := wordMux (zeroWord ((d.pair q).comp (mod w))) q
    (natSubOn q (wordConstant (BitVec.ofNat w 1)))
  (wordMux cond d v).pair (wordMux cond ((a.pair weight).comp (mul w)) a)

/-- Carry the input unchanged and update two finite-word accumulators. -/
def totientUpdate {k w : ℕ} (q : BooleanNetwork k w) :
    BooleanNetwork (k+(w+w)) (k+(w+w)) :=
  (select (Fin.castAdd (w+w))).pair (totientPair (liftInput q (Fin.castAdd (w+w)))
    (select (fun i=>Fin.natAdd k (Fin.castAdd w i)))
    (select (fun i=>Fin.natAdd k (Fin.natAdd w i))))

def totientScanNet {k w : ℕ} : List (BooleanNetwork k w)→BooleanNetwork (k+(w+w)) (k+(w+w))
  | []=>select id
  | q::qs=>(totientUpdate q).comp (totientScanNet qs)

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

/-- Run the polynomial accumulator scan from the queried word and one. -/
def totientFromList {k w : ℕ} (v : BooleanNetwork k w) (qs : List (BooleanNetwork k w)) :
    BooleanNetwork k w :=
  (((select id).pair (v.pair (wordConstant (BitVec.ofNat w 1)))).comp
    (totientScanNet qs)).comp (select (fun i=>Fin.natAdd k (Fin.natAdd w i)))

/-- At most n repetitions of each rectangular prime entry suffice. Unlike
order stripping, the totient accumulator does not need a wide product. -/
def tableTotient {k n : ℕ} (v : BooleanNetwork k n)
    (rows : List (BooleanNetwork k n×List (BooleanNetwork k n))) : BooleanNetwork k n :=
  totientFromList v (List.flatten (List.replicate n (tableNets rows)))

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TableDirectPhi
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

def primesPhiNet {k n : ℕ} (m : BooleanNetwork k n) (ps : List (BooleanNetwork k n)) :
    BooleanNetwork k n := totientFromList m (List.flatten (List.replicate n ps))

end BitArithmetic
end ExactQuantumFactoring


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

/-- Compute the odd part by a bounded gcd and exact integer division. -/
def oddPartNet {k n : ℕ} (a : BooleanNetwork k n) : BooleanNetwork k n :=
  (a.pair (primeComponent a (wordConstant (BitVec.ofNat n 2)))).comp (div n)

/-- An exact level count, selected by the bounded divisibility predicate.
The branch at t≥n is zero since a is a nonzero n-bit word. -/
def closedLevelNet {k n : ℕ} (a : BooleanNetwork k n) (t : ℕ) : BooleanNetwork k n :=
  if t=0 then oddPartNet a
  else if t<n then wordMux (a.comp (dividesNet n (2^t)))
    (((oddPartNet a).pair (wordConstant (BitVec.ofNat n (2^(t-1))))).comp (mul n))
    (wordConstant (BitVec.ofNat n 0))
  else wordConstant (BitVec.ofNat n 0)

end BitArithmetic
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

/-- Euler's prime-power formula, implemented by n-bit arithmetic on the
computed gcd component. Divisibility by p is a verified-call precondition. -/
def componentPhiNet {k n : ℕ} (m p : BooleanNetwork k n) : BooleanNetwork k n :=
  let q:=primeComponent m p
  natSubOn q ((q.pair p).comp (div n))

def componentLevelNet {k n : ℕ} (m p : BooleanNetwork k n) (t : ℕ) : BooleanNetwork k n :=
  wordMux (dividesOn p m) (closedLevelNet (componentPhiNet m p) t)
    (wordConstant (BitVec.ofNat n 1))

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_DistinctProductCircuit
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

/-- Equality is tested on runtime word values, not on network syntax. -/
def occursLater {k n : ℕ} (p : BooleanNetwork k n) (ps : List (BooleanNetwork k n)) :
    BooleanNetwork k 1 := any (ps.map (fun q=>(p.pair q).comp (wordEq n)))

/-- A quadratic comparison scan counts every runtime prime only once.
No sorting primitive or mathematical finset operation is used by the circuit. -/
def distinctProductNet {k n : ℕ} (value : BooleanNetwork k n→BooleanNetwork k n) :
    List (BooleanNetwork k n)→BooleanNetwork k n
  | []=>wordConstant 1
  | p::ps=>(wordMux (occursLater p ps) (wordConstant 1) (value p)).pair
      (distinctProductNet value ps) |>.comp (mul n)

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TableLevelCircuit
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

def tableLevelNet {k n : ℕ} (m : BooleanNetwork k n) (ps : List (BooleanNetwork k n)) (t : ℕ) :
    BooleanNetwork k n := distinctProductNet (fun p=>componentLevelNet m p t) ps

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_WordSumCircuit
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

def sumNet {k w : ℕ} : List (BooleanNetwork k w)→BooleanNetwork k w
  | []=>wordConstant 0
  | a::as=>(a.pair (sumNet as)).comp (add w)

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

def tableBadCountNet {k n : ℕ} (m : BooleanNetwork k n) (ps : List (BooleanNetwork k n)) :
    BooleanNetwork k n := sumNet (List.ofFn (fun t : Fin (n+1)=>tableLevelNet m ps t.val))

/-- The exact source F, computed from supplied prime rows using polynomial
integer circuits. Distinctness tests remove repeated table entries. -/
def tableFavorableCountNet {k n : ℕ} (m : BooleanNetwork k n) (ps : List (BooleanNetwork k n)) :
    BooleanNetwork k n := natSubOn (primesPhiNet m ps) (tableBadCountNet m ps)

end BitArithmetic
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedFavorableCount
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
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

def retainedFavorableCount (t : ℕ) (m : BooleanNetwork (M.width t) n) :
    BooleanNetwork (M.width t) n := tableFavorableCountNet m (tableNets (M.fieldRows t))

end NodeMachine
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

namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

def listFilterVars (t : ℕ) (m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (PhysicalListSlots.width n)) :
    Fin 3→BooleanNetwork (M.width t) (listVarWidth n) := fun i=>
  if i=0 then m.comp (resizeWord n (listVarWidth n)) else
  if i=1 then (M.retainedFavorableCount t m).comp (resizeWord n (listVarWidth n)) else
  (raw.comp (Completion.retentionWires (PhysicalListSlots.ordinaryWidth n)
    (Completion.transitionWidth n) (2*n) (n*n^5))).comp (resizeWord (listCoinWidth n) (listVarWidth n))

def retainedListFilter (hn : 0<n) (t : ℕ) (m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (PhysicalListSlots.width n)) : BooleanNetwork (M.width t) 1 :=
  Completion.predicateFilter (W:=Completion.transitionWidth n) (n*n^5)
    (Completion.Expressions.listRateCoin n (n^5)) (RatExpr.const (Completion.target n))
    (M.listFilterVars t m raw)
    (raw.comp (Completion.rareWires (PhysicalListSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) (n*n^5))) (.var 2)
    (M.retainedGoodList t m ((raw.comp (Completion.ordinaryWires (PhysicalListSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) (n*n^5))).comp (PhysicalListSlots.ordinaryNet n)))
    (M.retainedCanonicalList hn t m (raw.comp (Completion.guessWires (PhysicalListSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) (n*n^5))))

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedListDummy
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
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

def listDummyFilter (t : ℕ) (m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (PhysicalListSlots.width n)) : BooleanNetwork (M.width t) 1 :=
  Completion.predicateFilter (W:=Completion.transitionWidth n) (n*n^5)
    (RatExpr.const 1) (RatExpr.const (Completion.target n)) (M.listFilterVars t m raw)
    (raw.comp (Completion.rareWires (PhysicalListSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) (n*n^5))) (.var 2)
    (constant true)
    (zeroWord (raw.comp (Completion.guessWires (PhysicalListSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) (n*n^5))))

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedTotient
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
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

/-- The totient network reads only the actual retained rectangular table. -/
def retainedTotient (t : ℕ) (v : BooleanNetwork (M.width t) n) :
    BooleanNetwork (M.width t) n := tableTotient v (M.fieldRows t)

/-- The numerator of the exact order-trial success probability, with no
recovery of an exponent record and no factorization call at runtime. -/
def retainedOrderPhi (t : ℕ) (a m : BooleanNetwork (M.width t) n) :
    BooleanNetwork (M.width t) n := M.retainedTotient t (M.retainedOrder t a m)

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
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

def orderFilterVars (t : ℕ) (a m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (OrderSlots.width n)) :
    Fin 3→BooleanNetwork (M.width t) (orderVarWidth n) := fun i=>
  if i=0 then (M.retainedOrder t a m).comp (resizeWord n (orderVarWidth n)) else
  if i=1 then (M.retainedOrderPhi t a m).comp (resizeWord n (orderVarWidth n)) else
  (raw.comp (Completion.retentionWires (OrderSlots.ordinaryWidth n)
    (Completion.transitionWidth n) (2*n) ((n+10)*n^5))).comp
      (resizeWord (OrderSlots.coinWidth n) (orderVarWidth n))

def orderActualFilter (t : ℕ) (a m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (OrderSlots.width n)) : BooleanNetwork (M.width t) 1 :=
  Completion.predicateFilter (W:=Completion.transitionWidth n) ((n+10)*n^5)
    (Completion.Expressions.orderRateCoin n (n^5)) (RatExpr.const (Completion.target n))
    (M.orderFilterVars t a m raw)
    (raw.comp (Completion.rareWires (OrderSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) ((n+10)*n^5))) (.var 2)
    (equalOn (OrderSlots.orderResultNet a m (raw.comp (Completion.ordinaryWires (OrderSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) ((n+10)*n^5)))) (M.retainedOrder t a m))
    (equalOn (raw.comp (Completion.guessWires (OrderSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) ((n+10)*n^5)))
      ((M.retainedOrder t a m).comp (resizeWord n (Completion.transitionWidth n))))

def orderDummyFilter (t : ℕ) (a m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (OrderSlots.width n)) : BooleanNetwork (M.width t) 1 :=
  Completion.predicateFilter (W:=Completion.transitionWidth n) ((n+10)*n^5)
    (RatExpr.const 1) (RatExpr.const (Completion.target n)) (M.orderFilterVars t a m raw)
    (raw.comp (Completion.rareWires (OrderSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) ((n+10)*n^5))) (.var 2)
    (constant true)
    (zeroWord (raw.comp (Completion.guessWires (OrderSlots.ordinaryWidth n)
      (Completion.transitionWidth n) (2*n) ((n+10)*n^5))))

def retainedOrderFilter (t : ℕ) (a m : BooleanNetwork (M.width t) n)
    (raw : BooleanNetwork (M.width t) (OrderSlots.width n)) : BooleanNetwork (M.width t) 1 :=
  ((OrderSlots.usableOn a m).band (M.orderActualFilter t a m raw)).bor
    ((OrderSlots.usableOn a m).bnot.band (M.orderDummyFilter t a m raw))

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetrospectiveSlots
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
open AuxiliaryTree OrderTrial

/-- Test the same completed order slot using the later supplied node record.
Unusable list entries (including out-of-range words) use the source dummy test. -/
noncomputable def dataOrderPassed {n : ℕ} (data : FactorData) (a m : Basis n)
    (r : OrderSlots.Result n) : Prop := by
  classical
  exact
  if residueUsable (bitsValue a).toNat (bitsValue m).toNat then
    Completion.test
      (fun x => orderResult (OrderSlots.sampleExponent n) n a m (n^5) x=
        dataOrder data (bitsValue a).toNat (bitsValue m).toNat)
      (fun y => y=natBasis _ (dataOrder data (bitsValue a).toNat (bitsValue m).toNat))
      (dataOrderSuccess data (bitsValue a).toNat (bitsValue m).toNat (n^5)) (Completion.target n) r
  else Completion.test (fun _=>True) (fun y=>y=natBasis _ 0) 1 (Completion.target n) r

noncomputable def dataSplitPassed {n : ℕ} (data : FactorData) (m : Basis n) (hn : 0<n)
    (r : UniversalSplit.Raw n) : Prop := by
  classical
  exact
  if UniversalSplit.Hard (bitsValue m).toNat then
    dataListPassed data m hn r.1 ∧ ∀ i,dataOrderPassed data (FixedSplit.bases r.1 i) m (r.2 i)
  else UniversalSplit.dummy r

end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedSplitFilter
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
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

def splitModulus (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n)) :=
  raw.comp (FixedSplit.modulusNet n)
def splitList (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n)) :=
  (raw.comp (FixedSplit.launchWires n)).comp (FixedSplit.listWires n)
def splitBase (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n)) (i : Fin (n^5)) :=
  raw.comp (FixedSplit.actualBaseNet i)
def splitOrder (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n)) (i : Fin (n^5)) :=
  raw.comp (FixedSplit.actualOrderRawNet i)

def splitActualFilter (hn : 0<n) (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n)) :
    BooleanNetwork (M.width t) 1 :=
  (M.retainedListFilter hn t (M.splitModulus t raw) (M.splitList t raw)).band
    (all (List.ofFn (fun i : Fin (n^5)=>M.retainedOrderFilter t (M.splitBase t raw i)
      (M.splitModulus t raw) (M.splitOrder t raw i))))

def splitDummyFilter (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n)) :
    BooleanNetwork (M.width t) 1 :=
  (M.listDummyFilter t (M.splitModulus t raw) (M.splitList t raw)).band
    (all (List.ofFn (fun i : Fin (n^5)=>M.orderDummyFilter t (M.splitBase t raw i)
      (M.splitModulus t raw) (M.splitOrder t raw i))))

def retainedSplitFilter (hn : 0<n) (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n)) :
    BooleanNetwork (M.width t) 1 :=
  ((UniversalSplit.hardOn (M.splitModulus t raw)).band (M.splitActualFilter hn t raw)).bor
    ((UniversalSplit.hardOn (M.splitModulus t raw)).bnot.band (M.splitDummyFilter t raw))

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetrospectiveNode
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
open BooleanNetwork BitArithmetic OrderTrial AuxiliaryTree

namespace NodeKernel
/-- Retrospective evaluation on the actual split trace, with one verified
read-only factor-data view for this physical node. The controller and all query
words are the same ones used by the physical run. -/
noncomputable def dataTests {n : ℕ} (q : Basis n) (d : FactorData) (hn : 0<n) :
    (t : ℕ)→SplitMachine.Trace n t→Prop
  | 0,_=>True
  | t+1,r=>dataTests q d hn t r.1 ∧ dataSplitPassed d
      ((PhysicalNode.query n (2*n)).eval
        ((PhysicalNode.machine n (2*n)).config (start q) t r.1)) hn r.2

noncomputable def dataPassed {n : ℕ} (q : Basis n) (d : FactorData) (hn : 0<n)
    (r : Raw n) : Prop := dataTests q d hn (2*n) r

end NodeKernel
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_SplitHistoryAccess
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
namespace SplitMachine
variable {n c : ℕ} (M : SplitMachine n c)

def previousNet (t : ℕ) : BooleanNetwork (M.width (t+1)) (M.width t) :=
  (select (firstRegister (M.width t+FixedSplit.width n+M.initWork) c M.updateWork)).comp
    (select (firstRegister (M.width t) (FixedSplit.width n) M.initWork))
def lastSplitNet (t : ℕ) : BooleanNetwork (M.width (t+1)) (FixedSplit.width n) :=
  (select (firstRegister (M.width t+FixedSplit.width n+M.initWork) c M.updateWork)).comp
    (select (targetRegister (M.width t) (FixedSplit.width n) M.initWork))

end SplitMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedNodeFilter
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
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

def nodePrefixFilter (hn : 0<n) (T : ℕ) : (s : ℕ)→
    BooleanNetwork (M.width T) ((PhysicalNode.machine n (2*n)).width s)→BooleanNetwork (M.width T) 1
  | 0,_=>constant true
  | s+1,v=>(nodePrefixFilter hn T s (v.comp ((PhysicalNode.machine n (2*n)).previousNet s))).band
      (M.retainedSplitFilter hn T (v.comp ((PhysicalNode.machine n (2*n)).lastSplitNet s)))

def retainedNodeFilter (hn : 0<n) (T : ℕ)
    (raw : BooleanNetwork (M.width T) (NodeKernel.width n)) : BooleanNetwork (M.width T) 1 :=
  M.nodePrefixFilter hn T (2*n) raw

end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetrospectiveTree
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
open BooleanNetwork BitArithmetic OrderTrial AuxiliaryTree
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

/-- Read-only postprocessing of the retained actual history. Each node receives
only the flat row data at its actual runtime label. Occurrences are retained;
lookup selects the first matching verified record, not a factorization oracle. -/
noncomputable def dataTests (rows : List (ℕ×List ℕ)) (x : Basis c) (hn : 0<n) :
    (t : ℕ)→Trace n t→Prop
  | 0,_=>True
  | t+1,r=>dataTests rows x hn t r.1 ∧
    let q:=M.query.eval (M.config x t r.1)
    NodeKernel.dataPassed q (PhysicalTree.flatData rows (bitsValue q).toNat) hn r.2
end NodeMachine
namespace PhysicalTree

/-- Literal event specification for completed-data retrospective checking.
The Boolean implementation of the arithmetic and the whole polynomial-time
compiler are separate obligations, not consequences of this definition. -/
noncomputable def accepted {n N : ℕ} (hn : 0<n) (r : NodeMachine.Trace n (2*n^2)) : Prop :=
  (machine n).verified (initialQueue n N) (2*n^2) r ∧
    (machine n).dataTests ((machine n).dataLog (initialQueue n N) (2*n^2) r)
      (initialQueue n N) hn (2*n^2) r

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedTreeFilter
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
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

def treePrefixFilter (hn : 0<n) (T : ℕ) : (s : ℕ)→
    BooleanNetwork (M.width T) (M.width s)→BooleanNetwork (M.width T) 1
  | 0,_=>constant true
  | s+1,v=>(treePrefixFilter hn T s (v.comp (M.previousNet s))).band
      (M.retainedNodeFilter hn T (v.comp (M.lastNodeNet s)))

def acceptedNet (hn : 0<n) (T : ℕ) : BooleanNetwork (M.width T) 1 :=
  (M.verifiedNet T).band (M.treePrefixFilter hn T T (select id))
end NodeMachine
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_QuarterPreparation
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
open Exactness OrderTrial

namespace Quarter
abbrev Raw (α : Type*) (n : ℕ) := Completion.Raw α (n*n) 1 (n^11)
noncomputable def fresh {α : Type*} (ψ : α→ℂ) (n : ℕ) : Raw α n→ℂ :=
  Completion.fresh ψ (n*n) 1 (n^11)

def ordinaryPass {α : Type*} {n : ℕ} (success : α→Prop) (r : Raw α n) : Prop :=
  ¬Completion.rare r.1 ∧ (success r.2.1 ∧ Completion.threshold (retention n) r.2.2.2)
def guessPass {α : Type*} {n : ℕ} (N : ℕ) (r : Raw α n) : Prop :=
  Completion.rare r.1 ∧ (CorrectEncoding N n (guessWords n r.2.2.1) ∧
    Completion.threshold (guessRetention n) r.2.2.2)
def passed {α : Type*} {n : ℕ} (N : ℕ) (success : α→Prop) (r : Raw α n) : Prop :=
  ordinaryPass success r ∨ guessPass N r

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

abbrev PadRaw (n : ℕ) := Fin (padding n)→Basis n
noncomputable def padState (n : ℕ) : PadRaw n→ℂ := tensorState (fairState n) (padding n)
def padPassed {n : ℕ} (x : PadRaw n) : Prop := ∀ i, ¬ Completion.rare (x i)

abbrev PaddedRaw (n : ℕ) := NodeMachine.Trace n (2*n^2)×PadRaw n
noncomputable def paddedState (n N : ℕ) : PaddedRaw n→ℂ :=
  independentState ((machine n).state (initialQueue n N) (2*n^2)) (padState n)
noncomputable def paddedAccepted {n N : ℕ} (hn : 0<n) (x : PaddedRaw n) : Prop :=
  accepted (N:=N) hn x.1 ∧ padPassed x.2

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreePhysicalPreparation
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
open BooleanNetwork BitArithmetic Exactness OrderTrial

namespace PhysicalTree
abbrev launchWork (n : ℕ) := (initialNet n).net.count
abbrev launchWidth (n : ℕ) := n+width n+launchWork n

def launchProgram (n : ℕ) : List (Instruction (launchWidth n)) :=
  preparedOracle (initialNet n) le_rfl ((machine n).program (steps n))
def launchEncoding (n N : ℕ) (r : NodeMachine.Trace n (steps n)) : Basis (launchWidth n) :=
  packed (launchWork n) (natBasis n N) ((machine n).encoded (initialQueue n N) (steps n) r)
def launchZero (n N : ℕ) : Basis (launchWidth n) :=
  packed (launchWork n) (natBasis n N) (fun _=>false)

abbrev paddedWidth (n : ℕ) := launchWidth n+tensorWidth n (padding n)
def paddedProgram (n : ℕ) : List (Instruction (paddedWidth n)) :=
  parallelProgram (launchProgram n) (padProgram n)
def paddedZero (n N : ℕ) : Basis (paddedWidth n) :=
  Fin.append (launchZero n N) (tensorLayout n (padding n) (fun _ _=>false))
def paddedEncoding (n N : ℕ) (r : PaddedRaw n) : Basis (paddedWidth n) :=
  Fin.append (launchEncoding n N r.1) (tensorLayout n (padding n) r.2)

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeQuarterPhysical
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

namespace Completion
/-- The actual four-register completion, when the ordinary preparation has
retained and injectively encoded its full history. -/
def extendEncoding {α : Type*} {q : ℕ} (e : α→Basis q) (W t d : ℕ) :
    Raw α W t d→Basis (t+(q+(W+coinBits W t d))) :=
  fun r=>Fin.append r.1 (Fin.append (e r.2.1) (Fin.append r.2.2.1 r.2.2.2))

end Completion

namespace PhysicalTree
abbrev quarterWidth (n : ℕ) := 1+(paddedWidth n+(n*n+Quarter.D n))
def quarterProgram (n : ℕ) : List (Instruction (quarterWidth n)) :=
  Quarter.program (paddedProgram n) n
def quarterZero (n N : ℕ) : Basis (quarterWidth n) :=
  Completion.layout (paddedWidth n) (n*n) 1 (n^11)
    ((fun _=>false),paddedZero n N,(fun _=>false),(fun _=>false))
def quarterEncoding (n N : ℕ) : Quarter.Raw (PaddedRaw n) n→Basis (quarterWidth n) :=
  Completion.extendEncoding (paddedEncoding n N) (n*n) 1 (n^11)

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeRootOutput
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

/-- Only a fixed rearrangement of output wires, from tensor grouping to the
source's consecutive n-bit fields. No factor search is present. -/
def flattenWords (n : ℕ) : BooleanNetwork (tensorWidth n n) (n*n) :=
  wordBlocks (fun i=>tensorSelect n n i)

/-- A literal bounded readout for every clock count, with a harmless zero case. -/
def rootFlat (n : ℕ) : (t : ℕ)→BooleanNetwork ((machine n).width t) (n*n)
  | 0=>Completion.zeros _ _
  | t+1=>(rootResult n t).comp (flattenWords n)

noncomputable def ordinaryOutput (n N : ℕ) (r : PaddedRaw n) : Basis (n*n) :=
  (rootFlat n (2*n^2)).eval ((machine n).encoded (initialQueue n N) (2*n^2) r.1)

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_RetainedQuarterFilter
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

def launchHistory (n : ℕ) : BooleanNetwork (launchWidth n) (width n) :=
  select (targetRegister n (width n) (launchWork n))
def launchInput (n : ℕ) : BooleanNetwork (launchWidth n) n :=
  select (firstRegister n (width n) (launchWork n))
def paddedHistory (n : ℕ) : BooleanNetwork (paddedWidth n) (width n) :=
  (select (Fin.castAdd (tensorWidth n (padding n)))).comp (launchHistory n)
def paddedInput (n : ℕ) : BooleanNetwork (paddedWidth n) n :=
  (select (Fin.castAdd (tensorWidth n (padding n)))).comp (launchInput n)
def paddedPad (n : ℕ) : BooleanNetwork (paddedWidth n) (tensorWidth n (padding n)) :=
  select (Fin.natAdd (launchWidth n))

def padFlag (n : ℕ) : BooleanNetwork (tensorWidth n (padding n)) 1 :=
  all (List.ofFn (fun i : Fin (padding n)=>(zeroWord (tensorSelect n (padding n) i)).bnot))

def paddedFlag (n : ℕ) (hn : 0<n) : BooleanNetwork (paddedWidth n) 1 :=
  ((paddedHistory n).comp ((machine n).acceptedNet hn (2*n^2))).band
    ((paddedPad n).comp (padFlag n))

def quarterOrd (n : ℕ) := Completion.ordinaryWires (paddedWidth n) (n*n) 1 (n^11)
def quarterGuess (n : ℕ) := Completion.guessWires (paddedWidth n) (n*n) 1 (n^11)
def quarterCoin (n : ℕ) := Completion.retentionWires (paddedWidth n) (n*n) 1 (n^11)
def quarterRare (n : ℕ) := Completion.rareNet (paddedWidth n) (n*n) 1 (n^11)

def quarterKeep (n : ℕ) (p : ℚ) : BooleanNetwork (quarterWidth n) 1 :=
  retentionNet (Quarter.D n) (.const p) (.var ()) (fun _ : Unit=>quarterCoin n)

def quarterGuessFlag (n : ℕ) : BooleanNetwork (quarterWidth n) 1 :=
  ((((quarterOrd n).comp (paddedInput n)).pair (quarterGuess n))).comp (guessVerifier n)

def quarterFlag (n : ℕ) (hn : 0<n) : BooleanNetwork (quarterWidth n) 1 :=
  ((quarterRare n).bnot.band
    (((quarterOrd n).comp (paddedFlag n hn)).band (quarterKeep n (Quarter.retention n)))).bor
    ((quarterRare n).band ((quarterGuessFlag n).band (quarterKeep n (Quarter.guessRetention n))))

def paddedOutputNet (n : ℕ) : BooleanNetwork (paddedWidth n) (n*n) :=
  (paddedHistory n).comp (rootFlat n (2*n^2))
def quarterOutputNet (n : ℕ) : BooleanNetwork (quarterWidth n) (n*n) :=
  Completion.outputNet (paddedOutputNet n) 1 (n^11)

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeReadOnly
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
open BooleanNetwork Exactness

namespace PhysicalTree

/-- The original input is the n-wire interval immediately following the
fresh branch coin. This definition is independent of N. -/
def inputWires (n : ℕ) : Finset (Fin (quarterWidth n)) :=
  Finset.univ.filter (fun i => 1 ≤ i.val ∧ i.val < 1+n)

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ZeroOutside
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
open BooleanNetwork Exactness

/-- A linear-size clean-work flag, leaving every protected input bit alone. -/
def zeroOutside {q : ℕ} (I : Finset (Fin q)) : BooleanNetwork q 1 :=
  all (List.ofFn (fun i : Fin q => if i∈I then constant true else (bit i).bnot))

namespace PhysicalTree

/-- The zero reflection's flag depends only on the length and the actual clean
work coordinates, never on the unknown integer or its factorization. -/
def zeroNet (n : ℕ) : BooleanNetwork (quarterWidth n) 1 := zeroOutside (inputWires n)

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeAmplified
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

def reflectWork (n : ℕ) (hn : 0<n) : ℕ :=
  max (quarterFlag n hn).net.count (zeroNet n).net.count
abbrev amplifiedWidth (n : ℕ) (hn : 0<n) := quarterWidth n+1+reflectWork n hn

def amplifiedProgram (n : ℕ) (hn : 0<n) : List (Instruction (amplifiedWidth n hn)) :=
  amplificationProgram (quarterProgram n) (quarterFlag n hn) (zeroNet n)
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)
def amplifiedZero (n N : ℕ) (hn : 0<n) : Basis (amplifiedWidth n hn) :=
  packed (reflectWork n hn) (quarterZero n N) (fun _=>false)
def amplifiedOutput (n : ℕ) (hn : 0<n) : BooleanNetwork (amplifiedWidth n hn) (n*n) :=
  (select (firstRegister (quarterWidth n) 1 (reflectWork n hn))).comp (quarterOutputNet n)

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeReadout
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

/-- The readout is a clean reversible Boolean network, not a classical hidden
postprocessor. The preparation's complete history is retained. -/
def readoutProgram {q m r : ℕ} (P : List (Instruction q))
    (c : BooleanNetwork q m) (hr : c.net.count ≤ r) : List (Instruction (q+m+r)) :=
  firstProgram m r P++oracleOn c hr

namespace PhysicalTree
abbrev readoutWork (n : ℕ) (hn : 0<n) := (amplifiedOutput n hn).net.count
abbrev readoutWidth (n : ℕ) (hn : 0<n) := amplifiedWidth n hn+n*n+readoutWork n hn

def factoringProgram (n : ℕ) (hn : 0<n) : List (Instruction (readoutWidth n hn)) :=
  readoutProgram (amplifiedProgram n hn) (amplifiedOutput n hn) le_rfl
def factoringZero (n N : ℕ) (hn : 0<n) : Basis (readoutWidth n hn) :=
  packed (readoutWork n hn) (amplifiedZero n N hn) (fun _=>false)
def factoringResult (n : ℕ) (hn : 0<n) (x : Basis (readoutWidth n hn)) : Basis (n*n) :=
  x ∘ targetRegister (amplifiedWidth n hn) (n*n) (readoutWork n hn)

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CircuitProgramEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring

namespace CircuitEmission
open BitStackProgram BitStackProgram.Procedure BitStackProgram.Emits

namespace Emission
noncomputable def oracleOnOpsP : Procedure NetworkEmission.dataCode (listCode opCode) oracleOnOps:=by
  let env:=NetworkEmission.Emission.dataInputP.pair
    (((listLength Nat.bits 0).comp NetworkEmission.Emission.dataOutputsP).pair NetworkEmission.Emission.dataWidthP)
  exact (opsMapWith (f:=fun (e:ℕ×ℕ×ℕ) i=>BooleanNetwork.oracleIndex e.1 e.2.1 e.2.2 i) oracleIndexP).comp (env.pair oracleOpsP)
noncomputable def phaseOpP : Procedure Nat.bits opCode phaseOp:=
  opPackP.comp ((constant Nat.bits gateCode (plainGate .phase)).pair
    ((listCons Nat.bits).comp ((identity Nat.bits).pair (constant Nat.bits (listCode Nat.bits) []))))
noncomputable def phaseOpsP : Procedure NetworkEmission.dataCode (listCode opCode) phaseOps:=by
  let p:=phaseOpP.comp NetworkEmission.Emission.dataInputP
  let mid:=(listCons opCode).comp (p.pair ((listCons opCode).comp (p.pair (constant _ (listCode opCode) []))))
  exact opsAppendP.comp ((opsAppendP.comp (oracleOnOpsP.pair mid)).pair oracleOnOpsP)
end Emission

abbrev OpsEmits {α : Type} (ea : α→List Bool) {q : α→ℕ} (p : ∀x,List (Instruction (q x))) : Prop:=
  Emits ea (listCode opCode) (fun x=>(p x).map eraseOp)
end CircuitEmission
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_FactoringInputLayout
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

/-- The sole nondeterministic-preparation branch bit precedes the retained N;
all remaining physical input coordinates are clean. -/
def shiftedInput (q n N : ℕ) : Basis q :=
  fun i=>if 1 ≤ i.val ∧ i.val < 1+n then N.testBit (i.val-1) else false

namespace PhysicalTree

lemma quarterWidth_input (n : ℕ) : 1+n≤quarterWidth n := by
  change 1+n≤1+(n+width n+launchWork n+tensorWidth n (padding n)+(n*n+Quarter.D n))
  omega

end PhysicalTree
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

lemma finalRegister_bound (ℓ : ℕ) :
    ℓ+1≤amplifiedWidth (paddedLength ℓ) (paddedLength_pos ℓ) := by
  have h:=quarterWidth_input (paddedLength ℓ)
  have hl : ℓ≤paddedLength ℓ:=le_max_right _ _
  change ℓ+1≤quarterWidth (paddedLength ℓ)+1+reflectWork (paddedLength ℓ) (paddedLength_pos ℓ)
  omega

def finalRegister (ℓ : ℕ) : Register
    (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ))
    (readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ)) :=
  relocate (amplifiedWidth (paddedLength ℓ) (paddedLength_pos ℓ))
    (paddedLength ℓ*paddedLength ℓ) ℓ
    (readoutWork (paddedLength ℓ) (paddedLength_pos ℓ)) (finalRegister_bound ℓ)

def finalCircuit (ℓ : ℕ) : Circuit where
  qubits:=readoutWidth (paddedLength ℓ) (paddedLength_pos ℓ)
  instructions:=(factoringProgram (paddedLength ℓ) (paddedLength_pos ℓ)).map
    (Instruction.place (finalRegister ℓ))

end PhysicalTree
end ExactQuantumFactoring


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CircuitPreparationEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Emits

namespace Emission
open Procedure
noncomputable def hadamardOpP : Procedure Nat.bits opCode hadamardOp:=by
  let wires:=(listCons Nat.bits).comp ((identity Nat.bits).pair (Procedure.constant _ (listCode Nat.bits) []))
  exact opPackP.comp ((Procedure.constant _ gateCode (plainGate .hadamard)).pair wires)
noncomputable def hadamardPrefixP : Procedure unaryCode (listCode opCode)
    (fun k=>(List.range k).map hadamardOp):=
  (listMap 0 (hadamardOp 0) hadamardOpP).comp NetworkEmission.Emission.rangeP
end Emission
end ExactQuantumFactoring.CircuitEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkLoopEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure
namespace Emission
noncomputable def foldRightPack {f : Pack→Pack→Pack} (c : ℕ)
    (h : ∀a b,(f a b).val.budget=a.val.budget+b.val.budget+c)
    (p : Procedure (prodCode packCode packCode) packCode (fun x=>f x.1 x.2)) :
    Procedure (prodCode (listCode packCode) packCode) packCode (fun x=>x.1.foldr f x.2):=by
  let fold:=foldList emptyPack p (Polynomial.C 104*(Polynomial.C (c+1)*Polynomial.X+1)^2) (by
    intro xs a i
    have hh:=packCode_bound ((xs.take i).foldl (fun b a=>f a b) a)
    rw [fold_budget_extra f c h] at hh
    have hb:=packBudget_le_code a
    have hx:=(packBudgets_le_code (xs.take i)).trans (listCode_length_take_le packCode i xs)
    have hl:=(list_length_le_code packCode (xs.take i)).trans (listCode_length_take_le packCode i xs)
    have hm:=Nat.pow_le_pow_left (show a.val.budget+((xs.take i).map (fun s=>s.val.budget)).sum+c*(xs.take i).length+1≤
      (c+1)*((listCode packCode xs).length+(packCode a).length)+1 by nlinarith) 2
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    exact hh.trans (Nat.mul_le_mul_left _ hm))
  let input:=((listReverse packCode emptyPack).comp (first (listCode packCode) packCode)).pair
    (second (listCode packCode) packCode)
  exact (fold.comp input).congrFun (by intro x;exact List.foldl_reverse)
noncomputable def allPackP : Procedure (prodCode unaryCode (listCode packCode)) packCode
    (fun x=>x.2.foldr bandPack (constantPack x.1 true)):=by
  let start:=constantPackP.comp ((first unaryCode (listCode packCode)).pair (Procedure.constant _ boolCode true))
  exact (foldRightPack 4 (by intros;rfl) bandPackP).comp ((second unaryCode (listCode packCode)).pair start)
noncomputable def anyPackP : Procedure (prodCode unaryCode (listCode packCode)) packCode
    (fun x=>x.2.foldr borPack (constantPack x.1 false)):=by
  let start:=constantPackP.comp ((first unaryCode (listCode packCode)).pair (Procedure.constant _ boolCode false))
  exact (foldRightPack 13 (by intros;dsimp [borPack,bnotPack,bandPack,compPack,pairPack,nodePack];omega) borPackP).comp
    ((second unaryCode (listCode packCode)).pair start)
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_CleanPermutationEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.CircuitEmission
open BitStackProgram BitStackProgram.Emits

noncomputable def swapOpsP : Procedure (prodCode Nat.bits Nat.bits) (listCode opCode) (fun x=>swapOps x.1 x.2):=by
  have hx:=BitStackProgram.Emits.id (prodCode Nat.bits Nat.bits)
  have hi:=hx.snd
  have hj:=hx.fst.natAdd hi
  have ha:=(ofProcedure Emission.cnotOpP).comp (hi.pair hj)
  have hb:=(ofProcedure Emission.cnotOpP).comp (hj.pair hi)
  exact Classical.choice (ha.listCons (hb.listCons (ha.listCons (const _ _ []))))
end ExactQuantumFactoring.CircuitEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkSequenceEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace Emission
open Procedure
noncomputable def foldReverseCompP : Procedure (prodCode (listCode packCode) packCode) packCode
    (fun x=>x.1.foldl (fun a b=>compPack b a) x.2):=
  foldPack (by intros;change _+_=_+_;omega)
    (compPackP.comp ((second packCode packCode).pair (first packCode packCode)))
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_ListSamplerEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.ListSamplerEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission CircuitEmission
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
noncomputable def maskOpP : Procedure (prodCode Nat.bits Nat.bits) opCode (fun x=>maskOp x.1 x.2):=by
  let he:=BitStackProgram.Emits.id (prodCode Nat.bits Nat.bits)
  have hwire:=he.snd.listCons ((he.fst.natAdd he.snd).listCons (const _ _ []))
  exact Classical.choice ((ofProcedure CircuitEmission.Emission.opPackP).comp ((const _ _ (⟨.hadamard,false,true⟩ : Gate)).pair hwire))
end ExactQuantumFactoring.ListSamplerEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkAt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic

def NetworkAt {α : Type*} (len : α→ℕ) {a b : α→ℕ}
    (f : ∀x,BooleanNetwork (a x) (b x)) : Prop := PolyAt len (fun x=>(f x).net.count)
end ExactQuantumFactoring

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkCanonicalEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace Emission
open Procedure
noncomputable def canonicalPackP : Procedure packCode packCode canonicalPack:=by
  let hv:=packValueP
  let hmass:=boundedUnary (massP.comp hv) packBudgetP (fun x=>x.property.2)
  exact (hmass.pair hv).result (by intro x;rfl)
end Emission
end ExactQuantumFactoring.NetworkEmission

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
open BitStackProgram BitStackProgram.Procedure
lemma foldChoice_budget (c : Pack) (xs : List Pack) (b : Pack) :
    (xs.foldl (fun b a=>compPack (pairPack a b) c) b).val.budget=
      b.val.budget+(xs.map (fun a=>a.val.budget)).sum+c.val.budget*xs.length:=by
  exact fold_budget_extra _ c.val.budget (by intros;rfl) _ _
lemma foldChoice_state (xs : List Pack) (c b : Pack) :
    xs.foldl (fun s a=>(s.1,compPack (pairPack a s.2) s.1)) (c,b)=
      (c,xs.foldl (fun b a=>compPack (pairPack a b) c) b):=by
  induction xs generalizing b with
  | nil=>rfl
  | cons a xs ih=>simpa only [List.foldl_cons] using ih (compPack (pairPack a b) c)
lemma foldChoice_code_bound (xs : List Pack) (a : Pack×Pack) (i : ℕ) :
    (prodCode packCode packCode ((xs.take i).foldl (fun s a=>(s.1,compPack (pairPack a s.2) s.1)) a)).length ≤
      1000*((listCode packCode xs).length+(prodCode packCode packCode a).length+1)^4:=by
  rw [show a=(a.1,a.2) from rfl,foldChoice_state]
  simp only [prodCode,pairBits_length]
  have hc:=packCode_bound a.1
  have hb:=packCode_bound ((xs.take i).foldl (fun b t=>compPack (pairPack t b) a.1) a.2)
  rw [foldChoice_budget] at hb
  have ha:=packBudget_le_code a.1
  have ha':=packBudget_le_code a.2
  have hx:=(packBudgets_le_code (xs.take i)).trans (listCode_length_take_le packCode i xs)
  have hl:=(list_length_le_code packCode (xs.take i)).trans (listCode_length_take_le packCode i xs)
  have H:=quadBudget_bound _ _ _ _ _ _ _ ha ha' hl hx
  calc
    _ ≤ 2*(104*(a.1.val.budget+1)^2)+104*(a.2.val.budget+((xs.take i).map (fun t=>t.val.budget)).sum+a.1.val.budget*(xs.take i).length+1)^2+1 := by omega
    _ ≤ _ := by simpa only [Nat.add_assoc] using H
namespace Emission
noncomputable def foldChoiceStepP : Procedure (prodCode packCode (prodCode packCode packCode))
    (prodCode packCode packCode) (fun x=>(x.2.1,compPack (pairPack x.1 x.2.2) x.2.1)):=by
  let ex:=first packCode (prodCode packCode packCode)
  let st:=second packCode (prodCode packCode packCode)
  let sc:=(first packCode packCode).comp st
  let sb:=(second packCode packCode).comp st
  exact sc.pair (compPackP.comp ((pairPackP.comp (ex.pair sb)).pair sc))
noncomputable def foldChoiceP : Procedure
    (prodCode (listCode packCode) (prodCode packCode packCode)) packCode
    (fun x=>x.1.foldr (fun a b=>compPack (pairPack a b) x.2.1) x.2.2):=by
  let fold:=foldList emptyPack foldChoiceStepP
    (Polynomial.C 1000*(Polynomial.X+1)^4) (by
      intro xs a i
      simpa only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
        using foldChoice_code_bound xs a i)
  let inp:=((listReverse packCode emptyPack).comp (first (listCode packCode) (prodCode packCode packCode))).pair
    (second (listCode packCode) (prodCode packCode packCode))
  exact ((second packCode packCode).comp (fold.comp inp)).congrFun (by
    intro x;change (x.1.reverse.foldl (fun s a=>(s.1,compPack (pairPack a s.2) s.1)) x.2).2 = _
    rw [show x.2=(x.2.1,x.2.2) from rfl,foldChoice_state];exact List.foldl_reverse)
end Emission
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NetworkListEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
abbrev NetsEmits {α : Type} (ea : α→List Bool) {n m : α→ℕ}
    (f : ∀x,List (BooleanNetwork (n x) (m x))) : Prop:=
  Emits ea (listCode packCode) (fun x=>(f x).map erasePack)
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_DescendingFilterEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BooleanNetwork BitStackProgram BitStackProgram.Emits
def FilterState.positiveView {k : ℕ} {w : ℕ→ℕ} (r : FilterState k w) (h : 0 < r.depth) :
    Σs,BooleanNetwork k (w (s+1)) × List (BooleanNetwork k 1):=by
  cases r with | mk d v ps=>cases d with
    | zero=>exact False.elim (Nat.not_lt_zero _ h)
    | succ s=>exact ⟨s,v,ps⟩
end ExactQuantumFactoring.NetworkEmission

end



end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_NodeControlBounds
attribute [-simp] _root_.OAI.ExactQuantumFactoring.BitArithmetic.liftInput_count _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_gate _root_.OAI.ExactQuantumFactoring.NativeAIG.refVec_get_invert
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

@[simp] lemma pending_count (s w : ℕ) : (pending s w).net.count=0 := rfl
@[simp] lemma top_count (s w : ℕ) : (top s w).net.count=0 := rfl
@[simp] lemma divisor_count (s w : ℕ) : (divisor s w).net.count=0 := rfl

end NodeCircuit
end ExactQuantumFactoring.BitArithmetic


end

end OAI
end

section
-- module Solutions.OAIQ222_QF.QuantumFactoring_TreeTableEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.Emission
open BitStackProgram BitStackProgram.Procedure
noncomputable def compRowP : Procedure (prodCode packCode rowCode) rowCode (fun x=>compRow x.1 x.2):=by
  let a:=first packCode rowCode
  let r:=second packCode rowCode
  let b:=(first packCode packCode).comp r
  let c:=(second packCode packCode).comp r
  exact (canonicalPackP.comp (compPackP.comp (a.pair b))).pair (canonicalPackP.comp (compPackP.comp (a.pair c)))
end ExactQuantumFactoring.NetworkEmission.Emission
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission
variable {α : Type} {ea : α→List Bool} {n t : α→ℕ}
def packedLog (n t : ℕ) : List (Pack×Pack):=
  ((PhysicalTree.machine n).logNets t).map (fun r=>(erasePack r.1,erasePack r.2))

end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
end


