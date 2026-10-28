-- Prove2me | Definitions.Def_OAIQ087A023
-- name    : OAIQ087A023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:36:42.505005+00:00
-- url     : https://prove2.me/theorems/d0e6d4e4-5960-467c-b8a0-7f7ba87ad22b
-- title:
--   Definitions bundle OAIQ087A023 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 348 declarations of OpenAI's Lean: 95 definitions, 7 inductive types or structures, 1 instance and 245 theorems. The definitions and types are `OAI.MaxCutGames.Explicit.ProductPaddedOutput.finalCoordinates`, `OAI.MaxCutGames.Explicit.ProductTarget.render_simpleBipartite`, `OAI.MaxCutGames.Explicit.SubdivisionTarget.simpleBipartite`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program.auxiliaryFlag`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program.headFlag`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program.headerPlan`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program.machine`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program.program`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program.referenceOffset`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program.referenceValue`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program.tailFlag`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFPattern.tableVerifier`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFTemplate.resolve`, `OAI.MaxCutGames.Foundations.Complexity.GraphCounterFinish.finishInTime`, `OAI.MaxCutGames.Foundations.Complexity.GraphCounterPrefix.count`, `OAI.MaxCutGames.Foundations.Complexity.GraphIterationBounds.count`, `OAI.MaxCutGames.Foundations.Complexity.GraphIterationBounds.inputBits`, `OAI.MaxCutGames.Foundations.Complexity.GraphIterationBounds.lengthPolynomial`, `OAI.MaxCutGames.Foundations.Complexity.GraphIterationBounds.runtimePolynomial`, `OAI.MaxCutGames.Foundations.Complexity.GraphIterationBounds.words`, `OAI.MaxCutGames.Foundations.Complexity.MachineCanonicalOutput.TerminalRun`, `OAI.MaxCutGames.Foundations.Complexity.MachineCanonicalOutput.completedMachine`, `OAI.MaxCutGames.Foundations.Complexity.MachineCanonicalOutput.completedProgram`, `OAI.MaxCutGames.Foundations.Complexity.MachineCanonicalOutput.completedTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineCanonicalOutput.embeddedCfg`, `OAI.MaxCutGames.Foundations.Complexity.MachineCeilingPower.paddingInTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudPadding.padding`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudPadding.program`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudPrefix.amount`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudPrefix.bodyTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudPrefix.cycleTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudPrefix.loopTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudPrefix.program`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudPrefix.sumFrom`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudPrefix.totalTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudRank.rankProgram`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudSelect.cloudSelectSteps`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudSelect.remainder`, `OAI.MaxCutGames.Foundations.Complexity.MachineDummyRows.fieldTapes`, `OAI.MaxCutGames.Foundations.Complexity.MachineDummyRows.initialTapes` and 62 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MaxCut_Games_FinalCNFPattern`, `MaxCut_Games_FinalCNFStream`, `MaxCut_Games_GraphIterationBounds`, `MaxCut_Games_Product`, `MaxCut_Games_ProductTarget`, `MaxCut_Games_TranslationTarget`, `MaxCut_Machines_CompareLoop`, `MaxCut_Machines_GraphCounterFinish`, `MaxCut_Machines_Input`, `MaxCut_Machines_Lookup`, `MaxCut_Machines_MachineCanonicalOutput`, `MaxCut_Machines_MachineCloudCount`, `MaxCut_Machines_MachineCloudPadding`, `MaxCut_Machines_MachineCloudPrefix`, `MaxCut_Machines_MachineCloudSelect`, `MaxCut_Machines_MachineDummyRows`, `MaxCut_Machines_MachineExpanderFamilyAffine`, `MaxCut_Machines_MachineExpanderFamilyCycle`, `MaxCut_Machines_MachineExpanderRowFrames`, `MaxCut_Machines_MachineExpanderTableProgram`, `MaxCut_Machines_MachineExpanderTableRows`, `MaxCut_Machines_MachineLazyTableRuntime`, `MaxCut_Machines_MachineRegularLift`, `MaxCut_Machines_RawInitialMachineCleanup`, `MaxCut_Machines_Relations`, `MaxCut_PCP_ExpanderFamily`, `MaxCut_PCP_ExpanderRowControl`, `MaxCut_PCP_ExpanderTableEnumeration`, `MaxCut_PCP_FinalBooleanVerifier`, `MaxCut_PCP_GraphTableComplexity`, `MaxCut_PCP_PoweringOpinionTables`, `MaxCut_PCP_PreprocessingPaddingWords`, `MaxCut_PCP_PreprocessingRegularTables`, `MaxCut_PCP_RawInitialTables`, `MaxCut_PCP_RoundGap`, `MaxCut_PCP_SpectralCut`, `MaxCut_PCP_TableIteration`.
--
--   **Imports.** It imports the bundles `OAIQ087A014`, `OAIQ087A015`, `OAIQ087A016` and `OAIQ087A017` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ087A029`, `OAIQ087A030`, `OAIQ087A031` and `OAIQ087A032`.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ087A014
import Definitions.Def_OAIQ087A015
import Definitions.Def_OAIQ087A016
import Definitions.Def_OAIQ087A017

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_TranslationTarget
attribute [-instance] _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Explicit.UniformTarget

open MaxCutGames.Foundations Target Complexity
open MaxCutGames.Integration
open MachineUniformCopyOrder

theorem translations {q s : Nat} (C : Nat) (hC : 0 < C) (g : Instance q)
    (coordinates : Fin q ≃ BinaryLinear.Vector s)
    (hg : TranslationTarget.IsTranslationInstance coordinates g) :
    TranslationTarget.IsTranslationInstance coordinates (construct C hC g) := by
  intro c hc
  exact hg c (mem_original C hC g c hc)

end MaxCutGames.Explicit.UniformTarget

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ExpanderFamily
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A concrete finite family from the Cayley base

The initial graph has one vertex and the fixed number of loop ports. Each
subsequent graph is the actual square-and-zigzag construction. Consequently
the vertex sizes are exact powers of one fixed integer, including size one.
The finite base is selected from the proved existence theorem.
-/

/-!
# Padding actual tail fibers to the geometric graph-family sizes

Every nonempty cloud is padded to the next family size. Empty clouds stay
empty, so their old vertices do not create new darts. Explicit equivalences
identify padded tail fibers and partition all darts by their original tails.
These facts give the global size bound without an expansion assumption.
-/

/-!
# Executable indexing of the actual outgoing-dart clouds

Clouds are enumerated by filtering the input table's increasing dart-index
list. Ranking searches that list, and selection reads its indexed entry.
The same functions work for empty clouds without selecting a default dart.
Padded cloud indices put all old darts first and the dummy indices afterward.
All data functions below are executable; their proofs establish the connection
to the semantic graph's actual tail fibers.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingLevels

theorem boundedLevel_le_input (k : Nat) : boundedLevel k ≤ k := by
  simpa only [boundedLevel, searchResult, Nat.zero_add] using
    levelLoop_level_le ExpanderFamily.growth k k 0 1

theorem paddedSize_power (k : Nat) :
    paddedSize k = ExpanderFamily.growth ^ boundedLevel k := by
  simpa only [paddedSize, boundedLevel, searchResult, pow_zero] using
    levelLoop_power ExpanderFamily.growth k k 0

theorem le_paddedSize (k : Nat) : k ≤ paddedSize k := by
  exact levelLoop_covers ExpanderFamily.growth k k 0 1
    ExpanderFamily.growth_gt_one (by omega) (by omega)

/-- The bounded multiplication loop computes the existing ceiling logarithm. -/
theorem boundedLevel_eq_level (k : Nat) :
    boundedLevel k = ExpanderFamily.level k := by
  apply Nat.le_antisymm
  · simpa only [boundedLevel, searchResult, pow_zero] using
      levelLoop_le_of_covering_power ExpanderFamily.growth k k 0
        (ExpanderFamily.level k) (Nat.zero_le _) (ExpanderFamily.le_size k)
  · apply (Nat.clog_le_iff_le_pow ExpanderFamily.growth_gt_one).2
    rw [← paddedSize_power]
    exact le_paddedSize k

theorem paddedSize_eq_size (k : Nat) : paddedSize k = ExpanderFamily.size k := by
  rw [paddedSize_power, boundedLevel_eq_level]
  rfl

theorem paddedSize_positive (k : Nat) : 0 < paddedSize k := by
  rw [paddedSize_power]
  exact Nat.pow_pos (by have h := ExpanderFamily.growth_gt_one; omega)

/-- Positive cloud sizes and positive whole-graph vertex counts increase by
at most the single fixed growth factor. -/
theorem paddedSize_bounds {k : Nat} (hk : 0 < k) :
    k ≤ paddedSize k ∧ paddedSize k ≤ ExpanderFamily.growth * k := by
  rw [paddedSize_eq_size]
  exact ⟨ExpanderFamily.le_size k, ExpanderFamily.size_le_mul hk⟩

/-- Empty clouds remain empty; nonempty clouds use the geometric family. -/
def cloudPaddedSize (k : Nat) : Nat := if k = 0 then 0 else paddedSize k

@[simp] theorem cloudPaddedSize_zero : cloudPaddedSize 0 = 0 := rfl

theorem cloudPaddedSize_of_pos {k : Nat} (hk : 0 < k) :
    cloudPaddedSize k = paddedSize k := by
  simp only [cloudPaddedSize, Nat.ne_of_gt hk, ite_false]

theorem cloudPaddedSize_bounds (k : Nat) :
    k ≤ cloudPaddedSize k ∧ cloudPaddedSize k ≤ ExpanderFamily.growth * k := by
  by_cases hk : k = 0
  · subst k
    simp only [cloudPaddedSize_zero, Nat.mul_zero, le_refl, and_self]
  · rw [cloudPaddedSize_of_pos (Nat.pos_of_ne_zero hk)]
    exact paddedSize_bounds (Nat.pos_of_ne_zero hk)

/-- The executable table family has exactly the size returned by the loop. -/
theorem table_vertexCount_eq_paddedSize (k : Nat) :
    ExpanderTables.vertexCount (Expanders.baseDegree * Expanders.baseDegree)
        (boundedLevel k) = paddedSize k := by
  rw [ExpanderTables.vertexCount_eq]
  have hg : (Expanders.baseDegree * Expanders.baseDegree) *
      (Expanders.baseDegree * Expanders.baseDegree) = ExpanderFamily.growth := by
    unfold ExpanderFamily.growth
    ring
  rw [hg]
  exact (paddedSize_power k).symm

end MaxCutGames.Foundations.PCP.PreprocessingLevels

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingRegularTables
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Executable degree replacement on the actual finite constraint rows

Vertices are numbered by first listing the original darts, then the dummy
darts in original-vertex order. Each local cloud uses its explicit filtered
dart list. Internal ports carry equality; the final port retains the original
constraint, or an always-accepting loop at a dummy dart. The constructor is
total, including inputs with no darts. The fixed base expander is supplied
once; every input-dependent operation is an explicit finite calculation.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingRegularTables

open scoped BigOperators
open PoweringWalks DegreeReplacement

def padding (t : GraphTables.Table) (v : Fin t.vertices) : Nat :=
  PreprocessingLevels.cloudPaddedSize (PreprocessingCloudIndex.cloudSize t v) -
    PreprocessingCloudIndex.cloudSize t v

theorem cloudSize_add_padding (t : GraphTables.Table) (v : Fin t.vertices) :
    PreprocessingCloudIndex.cloudSize t v + padding t v =
      PreprocessingLevels.cloudPaddedSize (PreprocessingCloudIndex.cloudSize t v) :=
  Nat.add_sub_of_le (PreprocessingLevels.cloudPaddedSize_bounds _).1

theorem vertexCount_eq_sum_cloudPaddedSize (t : GraphTables.Table) :
    vertexCount t (padding t) = ∑ v,
      PreprocessingLevels.cloudPaddedSize (PreprocessingCloudIndex.cloudSize t v) := by
  unfold vertexCount
  rw [← PreprocessingCloudIndex.sum_cloudSize t, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun v _ => cloudSize_add_padding t v)

theorem vertexCount_le (t : GraphTables.Table) :
    vertexCount t (padding t) ≤ ExpanderFamily.growth * t.darts := by
  rw [vertexCount_eq_sum_cloudPaddedSize, ← PreprocessingCloudIndex.sum_cloudSize t,
    Finset.mul_sum]
  exact Finset.sum_le_sum (fun v _ => (PreprocessingLevels.cloudPaddedSize_bounds _).2)

/-- Select the family level by the bounded multiplication search. -/
def familyCloudTable (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices) :
    ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + padding t v)
      internalDegree :=
  if hk : PreprocessingCloudIndex.cloudSize t v = 0 then
    resizeTable (by rw [cloudSize_add_padding, hk]; rfl) (emptyTable internalDegree)
  else
    resizeTable (by
      rw [cloudSize_add_padding,
        PreprocessingLevels.cloudPaddedSize_of_pos (Nat.pos_of_ne_zero hk)]
      exact PreprocessingLevels.table_vertexCount_eq_paddedSize _)
      (ExpanderTables.family H
        (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v)))

/-- The actual regularized output rows; no runtime proof or positivity input. -/
def regularize (H : BaseTable) (t : GraphTables.Table) :
    PortTables.Table (vertexCount t (padding t)) (internalDegree + 1) :=
  ofCloudTables t (padding t) (familyCloudTable H t)

end MaxCutGames.Foundations.PCP.PreprocessingRegularTables

/-!
# Executable whole-vertex padding of regular constraint tables

The first `n` vertex rows retain their old rotation and complete relation
tables. Every additional vertex has one self-reversing, always-accepting loop
at each port. An explicit finite sum equivalence identifies these stored rows
with `VertexPadding.pad`; rejection counts are preserved for every labeling.

The construction materializes finite vectors. No machine runtime bound is
claimed here.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_SpectralCut
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual directed-cut expansion from the graph's zero-mean spectral
certificate. Parallel edges and loops retain their indexed port multiplicities. -/

/-!
An actual fixed-degree graph obtained by padding each outgoing-dart cloud to
the explicit expander family and then replacing vertices by cloud darts.
Expansion and majority rounding are proved dependencies, not hypotheses of
the final soundness theorem. Isolated original vertices have empty clouds.
-/

/-! Spectral contraction for the actual Boolean-flag lazy port graph. The
operator identity is proved in `PoweringLazy`; the estimate here averages the
elementary two-term square inequality. -/

/-!
# Concrete preprocessing table algorithm

Given one fixed expander base table, this function computes regularized
cloud rows, pads the whole vertex set, overlays a stored family table, and
adds the half-lazy rows. It is total even on zero-dart input tables. The
bounds below concern actual output data; an actual TM2 execution certificate
is a separate theorem and is not inferred from these size bounds.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingTables

open PreprocessingRegularTables

def regularVertices (t : GraphTables.Table) : Nat := vertexCount t (padding t)
def vertices (t : GraphTables.Table) : Nat := PreprocessingLevels.paddedSize (regularVertices t)

def padded (H : BaseTable) (t : GraphTables.Table) :
    PortTables.Table (vertices t) (internalDegree + 1) :=
  PreprocessingPaddingTables.pad (regularize H t)
    (PreprocessingLevels.le_paddedSize (regularVertices t))

def overlayFamily (H : BaseTable) (t : GraphTables.Table) :
    ExpanderTables.Table (vertices t) internalDegree :=
  resizeTable (PreprocessingLevels.table_vertexCount_eq_paddedSize (regularVertices t))
    (ExpanderTables.family H (PreprocessingLevels.boundedLevel (regularVertices t)))

def preprocess (H : BaseTable) (t : GraphTables.Table) :
    PortTables.Table (vertices t) degree :=
  PreprocessingOverlayTables.lazy
    (PreprocessingOverlayTables.overlay (padded H t) (overlayFamily H t))

theorem regularVertices_ge_darts (t : GraphTables.Table) : t.darts ≤ regularVertices t := by
  change t.darts ≤ t.darts + _
  omega

theorem regularVertices_le (t : GraphTables.Table) :
    regularVertices t ≤ ExpanderFamily.growth * t.darts := vertexCount_le t

theorem vertices_positive (t : GraphTables.Table) : 0 < vertices t :=
  PreprocessingLevels.paddedSize_positive _

theorem vertices_le_of_positive (t : GraphTables.Table) (ht : 0 < t.darts) :
    vertices t ≤ ExpanderFamily.growth ^ 2 * t.darts := by
  have hr : 0 < regularVertices t := ht.trans_le (regularVertices_ge_darts t)
  calc
    _ ≤ ExpanderFamily.growth * regularVertices t :=
      (PreprocessingLevels.paddedSize_bounds hr).2
    _ ≤ ExpanderFamily.growth * (ExpanderFamily.growth * t.darts) :=
      Nat.mul_le_mul_left _ (regularVertices_le t)
    _ = _ := by ring

end MaxCutGames.Foundations.PCP.PreprocessingTables

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PoweringOpinionTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounded first-address tables for actual powering constraints

For a graph with numbered vertices and ports, each stored local-opinion index
is the first address in `allAddresses` that reaches the requested vertex.
The search traverses bounded port words, never the ambient vertex set.

The walk table stores one base dart and two address indices per traversed
edge. Looking up the endpoint labels at those indices gives exactly the
existing `finitePortSelector` decoders, including when addresses collide.
The resulting finite table predicate equals the actual powering predicate.
-/

/-!
# Executable directed graph tables over a fixed finite alphabet

The alphabet size `q` is fixed by the encoding, not encoded as a variable input
field. The header stores vertex and directed-dart counts. Each ordered dart row
stores its tail, reverse index, and every `q*q` predicate bit in order `b+q*a`.
All fields use the existing unary natural-word codec. Decoding validates graph
laws and preserves loops and repeated darts. Size bounds count the complete
serialized table and make no running-time assertion.
-/

namespace MaxCutGames.Foundations.PCP.GenericGraphTables

open MaxCutGames.Foundations.Complexity

variable {q : Nat}

theorem darts_le_tableBits_length (table : (Table q)) :
    table.darts ≤ (tableBits table).length := by
  simp only [tableBits, tableWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

end MaxCutGames.Foundations.PCP.GenericGraphTables

/-!
# Executable tables of the actual powering graph

The input rotor and every base predicate are stored finite vectors. The output
has one row for each start vertex, bounded port word, and orientation, with the
two orientations adjacent. Every complete predicate table is generated from the
bounded first-address lookup test. Degree and walk length fix the output alphabet;
neither the alphabet nor an address list depends on the input vertex count.
-/

/-!
# Actual rejection counts and sizes for the powering construction

Normalized rejection averages are the cardinal ratios of the corresponding
rejected-dart sets. These identities include empty finite types. Positivity
of the dart cardinality is required only when translating inequalities by
division. The powered dart count and common alphabet size are computed from
their actual product and function types.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Relations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
# Real gap and exact size of the alphabet graph

The gap bound is obtained directly from the two checked rejection-count
inequalities. The finite graph's size is linear in the old vertices and darts,
with an explicit coefficient determined only by the old alphabet cardinality.
-/



namespace MaxCutGames.Foundations.PCP.AlphabetTableBounds

open AlphabetTable

variable {q : Nat}

/-- Exact output vertex count; this arithmetic identity also permits `q = 0`. -/
theorem build_vertices (input : GenericGraphTables.Table q) :
    (Table.build input).vertices = input.vertices * 2 ^ q +
      input.darts * AlphabetGraphBounds.vertexFactor q := by
  rw [Table.build_vertices]
  simp only [Enumeration.vertexCount, Enumeration.eventCount, Enumeration.addressCount,
    Enumeration.localCount, Enumeration.tapeCount, Enumeration.pairTapeCount,
    Enumeration.fiveTapeCount, AlphabetGraphBounds.vertexFactor,
    AlphabetGraphBounds.localEventFactor]
  ring

/-- Exact output dart count, including orientation and query multiplicity. -/
theorem build_darts (input : GenericGraphTables.Table q) :
    (Table.build input).darts = input.darts * AlphabetGraphBounds.dartFactor q := by
  rw [Table.build_darts]
  simp only [Enumeration.dartCount, Enumeration.eventCount, Enumeration.localCount,
    Enumeration.tapeCount, Enumeration.pairTapeCount, Enumeration.fiveTapeCount,
    AlphabetGraphBounds.dartFactor, AlphabetGraphBounds.localEventFactor]
  ring

theorem build_total (input : GenericGraphTables.Table q) :
    (Table.build input).vertices + (Table.build input).darts =
      input.vertices * 2 ^ q + input.darts *
        (AlphabetGraphBounds.vertexFactor q + AlphabetGraphBounds.dartFactor q) := by
  rw [build_vertices, build_darts]
  ring

/-- A fixed alphabet gives one linear bound on the actual output table size. -/
theorem build_total_le (input : GenericGraphTables.Table q) :
    (Table.build input).vertices + (Table.build input).darts ≤
      AlphabetGraphBounds.sizeFactor q * (input.vertices + input.darts) := by
  rw [build_total]
  have hv : 2 ^ q ≤ AlphabetGraphBounds.sizeFactor q := by
    unfold AlphabetGraphBounds.sizeFactor
    omega
  have he : AlphabetGraphBounds.vertexFactor q + AlphabetGraphBounds.dartFactor q ≤
      AlphabetGraphBounds.sizeFactor q := by
    unfold AlphabetGraphBounds.sizeFactor
    exact Nat.add_le_add_right (Nat.le_add_left _ _) _
  calc
    _ ≤ input.vertices * AlphabetGraphBounds.sizeFactor q +
        input.darts * AlphabetGraphBounds.sizeFactor q :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hv) (Nat.mul_le_mul_left _ he)
    _ = _ := by ring

end MaxCutGames.Foundations.PCP.AlphabetTableBounds

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_RawInitialTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit structural numberings of the raw 3SAT incidence graph. Unused
declared variable names are retained; their unary input header pays for them.
The graph has one dummy vertex and one tautological loop, even for an empty
formula. No input-dependent choice of a finite enumeration is made. -/

/-!
A stable type of finite graphs over one fixed alphabet. Vertex and dart types,
their finite enumeration and equality data, and the actual constraint graph
are stored together. The gap is computed from that graph's actual finite
labeling minimum. This mathematical bundle is not a serialized machine input;
no finite numbering is chosen here.
-/

/-! The concrete numbered amplification round, with one fixed base expander.
Every intermediate is an actual stored table, with explicit finite coordinates.
The running-time certificate is a separate theorem about these same functions. -/

namespace MaxCutGames.Foundations.PCP.RoundTables

def alphabet : Nat := PoweringTables.labelCount PreprocessingTables.degree walkParameter

def powered (H : BaseTable) (table : GraphTables.Table) : GenericGraphTables.Table alphabet :=
  PoweringTables.table (PreprocessingTables.preprocess H table) walkParameter

def build (H : BaseTable) (table : GraphTables.Table) : GraphTables.Table :=
  AlphabetTable.Table.build (powered H table)

def sizeFactor : Nat := AlphabetGraphBounds.sizeFactor alphabet *
  (ExpanderFamily.growth ^ 2 * (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1)))

theorem sizeFactor_positive : 0 < sizeFactor := by
  unfold sizeFactor
  apply Nat.mul_pos (AlphabetGraphBounds.sizeFactor_positive alphabet)
  apply Nat.mul_pos
  · exact Nat.pow_pos (Nat.zero_lt_one.trans ExpanderFamily.growth_gt_one)
  · omega

theorem powered_vertices (H : BaseTable) (table : GraphTables.Table) :
    (powered H table).vertices = PreprocessingTables.vertices table := rfl

theorem powered_darts (H : BaseTable) (table : GraphTables.Table) :
    (powered H table).darts = 2 * PreprocessingTables.vertices table *
      PreprocessingTables.degree ^ (walkParameter + 1) := rfl

theorem build_darts_positive (H : BaseTable) (table : GraphTables.Table) :
    0 < (build H table).darts := by
  change 0 < (AlphabetTable.Table.build (powered H table)).darts
  rw [AlphabetTableBounds.build_darts, powered_darts]
  exact Nat.mul_pos (Nat.mul_pos
    (Nat.mul_pos (by decide) (PreprocessingTables.vertices_positive table))
    (Nat.pow_pos degree_positive)) (dartFactor_positive alphabet)

theorem build_size_le (H : BaseTable) (table : GraphTables.Table)
    (ht : 0 < table.darts) :
    (build H table).vertices + (build H table).darts ≤
      sizeFactor * (table.vertices + table.darts) := by
  have hv := PreprocessingTables.vertices_le_of_positive table ht
  have he : (powered H table).vertices + (powered H table).darts =
      PreprocessingTables.vertices table *
        (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1)) := by
    rw [powered_vertices, powered_darts]
    ring
  have hp := Nat.mul_le_mul_right
    (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1)) hv
  calc
    _ ≤ AlphabetGraphBounds.sizeFactor alphabet *
        ((powered H table).vertices + (powered H table).darts) :=
      AlphabetTableBounds.build_total_le (powered H table)
    _ = AlphabetGraphBounds.sizeFactor alphabet *
        (PreprocessingTables.vertices table *
          (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1))) := by rw [he]
    _ ≤ AlphabetGraphBounds.sizeFactor alphabet *
        ((ExpanderFamily.growth ^ 2 * table.darts) *
          (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1))) :=
      Nat.mul_le_mul_left _ hp
    _ = sizeFactor * table.darts := by unfold sizeFactor; ring
    _ ≤ sizeFactor * (table.vertices + table.darts) :=
      Nat.mul_le_mul_left _ (Nat.le_add_left _ _)

abbrev Input := {table : GraphTables.Table // 0 < table.darts}

def step (H : BaseTable) (input : Input) : Input :=
  ⟨build H input.val, build_darts_positive H input.val⟩

def size (input : Input) : Nat := input.val.vertices + input.val.darts

theorem step_size (H : BaseTable) (input : Input) :
    size (step H input) ≤ sizeFactor * size input := build_size_le H input.val input.property

end MaxCutGames.Foundations.PCP.RoundTables

/-!
The finite iteration and size arithmetic for an amplification transformation.
The transformation itself must be supplied by the actual graph construction;
these theorems do not assert that such a transformation exists.  In particular,
the polynomial size estimate below is not a machine runtime certificate.
-/

namespace MaxCutGames.Foundations.PCP.VerifierToCNF

open Target

theorem freshIndex_value {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (j : Fin (q - 3)) :
    (freshIndex V e p j).val =
      V.«variables» + ((e.val * (patterns q).length + p.val) * (q - 3) + j.val) := by
  simp [freshIndex, Fin.natAdd, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

end MaxCutGames.Foundations.PCP.VerifierToCNF

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_FinalBooleanVerifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.PCP.FinalBooleanVerifier

open Target

variable {V E : Type*} {n m : Nat}

theorem query_tail (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (e : Fin m) (j : Fin 6) :
    (verifier G vertices edges).query e (Fin.castAdd 6 j) =
      bitIndex vertices (G.tail (edges.symm e)) j := by
  simp only [verifier, Fin.addCases_left]

theorem query_head (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (e : Fin m) (j : Fin 6) :
    (verifier G vertices edges).query e (Fin.natAdd 6 j) =
      bitIndex vertices (G.head (edges.symm e)) j := by
  simp only [verifier, Fin.addCases_right]

/-! Direct application to the checked alphabet-reduction graph. -/

end MaxCutGames.Foundations.PCP.FinalBooleanVerifier

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_FinalCNFPattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete relation addresses for the final Boolean verifier

Six-bit labels use the already checked executable little-endian enumeration.
A twelve-bit CNF pattern is split into its two endpoint labels, then addressed
in the graph table's row-major order. This fixed address map uses the actual
`VerifierToCNF.patternAt` enumeration, so no assumed correspondence between
two enumeration orders is needed. The graph interpretation is an explicit
relabeling of the validated table semantics.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFPattern

open PCP
open scoped BigOperators

/-- The concrete Boolean verifier associated with an already indexed table. -/
abbrev tableVerifier (table : GraphTables.Table) : VerifierToCNF.FiniteVerifier 12 :=
  FinalBooleanVerifier.verifier (tableGraph table) (Equiv.refl _) (Equiv.refl _)

theorem pattern_lookup_eq_verifier_accepts (table : GraphTables.Table)
    (e : Fin table.darts) (p : VerifierToCNF.PatternIndex 12) :
    table.rows[e].relation[patternRelationIndex p] =
      (tableVerifier table).accepts e (VerifierToCNF.patternAt 12 p) := rfl

end MaxCutGames.Foundations.Complexity.FinalCNFPattern

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Input
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Serialization boundaries and direct row lookup for the shared executable
fixed-alphabet graph codec. The alphabet is a fixed parameter. Rows remain in
their stored order, including repeated darts and loops. Word offsets are fixed;
bit offsets are represented by actual encoded prefixes because unary fields
have data-dependent lengths. These are data identities, not runtime certificates.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Input

open MaxCutGames.Foundations.Complexity

export GenericGraphTables (Label RelationTable DartRow Rows Valid Table
  relationIndex relationAt relationOf relationAt_relationOf
  reverseAt acceptsAt rowList rowList_length semantics semantics_reverse
  semantics_tail semantics_accepts ofGraph semantics_ofGraph ofEnumeratedGraph
  bitWord relationWords relationWords_length rowWords rowWords_length
  tableWords tableBits darts_le_tableBits_length)

variable {q n m : Nat}

/-- Removing precisely the two encoded header words exposes the stored rows. -/
theorem tableBits_header (table : Table q) :
    tableBits table = encodeWord table.vertices ++
      (encodeWord table.darts ++ encodeWords ((rowList table).flatMap rowWords)) := by
  simp [tableBits, tableWords, encodeWords]

end MaxCutGames.Foundations.PCP.AlphabetTable.Input

/-!
An actual fixed-alphabet TM2 parser for the complete Boolean relation table.
The finite syntax contains one slot reader for each of the `q*q` coordinates.
Each reader consumes `[false]` or `[true,false]`, stores the bit, and clears the
head register. No parser outcome or execution trace is an assumption.
-/

/-!
# An actual finite machine for a fixed-size Boolean block map

The program parameters `N`, `M`, and `F` are fixed. The local register has
exactly `N` bits. A syntactic chain of `N` pops fills that register, and a
syntactic chain of `M` pushes writes `F` of the register. No instruction
applies `F` to an unbounded word. An arbitrary ambient state is preserved,
and the local register is reset before the optional continuation.

TM2 executes a whole finite statement in one transition. The push bound
below separately records the exact `M` pushes in this statement.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Lookup
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Lookup

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K]

theorem rowBits_eq {q n m : Nat} (row : DartRow q n m) :
    rowBits row = encodeWord row.tail.val ++
      (encodeWord row.reverseIndex.val ++ encodeWords (relationWords row.relation)) := by
  simp [rowBits, rowWords, encodeWords]

def skipCost {q n m : Nat} (row : DartRow q n m) : Nat :=
  row.tail.val + row.reverseIndex.val + 4

def prefixCost {q n m : Nat} (rows : List (DartRow q n m)) : Nat :=
  (rows.map skipCost).sum

def lookupCost {q n m : Nat} (prior : List (DartRow q n m)) (row : DartRow q n m) : Nat :=
  prefixCost prior + row.tail.val + 3

section Ambient

variable {q n m : Nat} (counter source destination : K) (labels : Label → Λ)
  (exit : Option Λ)
  (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
  (atStatement : ∀ label, P (labels label) = statement q counter source destination labels exit label)

include atStatement

/-- One skipped row: two actual unary scans followed by one finite predicate
statement. All registers are reset and every other tape is untouched. -/
theorem skipRowTrace (base : K → List Bool) (row : DartRow q n m) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[row.tail.val + row.reverseIndex.val + 3]
      (some ⟨some (labels .skipTail), (ambient, register),
        Function.update base source (rowBits row ++ suffix)⟩) =
      some ⟨some (labels .guard), (ambient, none), Function.update base source suffix⟩ := by
  have ht := MachineLookup.discardTrace_update source (labels .skipTail) (labels .skipReverse)
    P (atStatement .skipTail) base row.tail.val
    (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
    ambient register
  have hr := MachineLookup.discardTrace_update source (labels .skipReverse) (labels .skipPredicate)
    P (atStatement .skipReverse) base row.reverseIndex.val
    (encodeWords (relationWords row.relation) ++ suffix) ambient none
  have hp : TM2.step P
      ⟨some (labels .skipPredicate), (ambient, none), Function.update base source
        (encodeWords (relationWords row.relation) ++ suffix)⟩ =
      some ⟨some (labels .guard), (ambient, none), Function.update base source suffix⟩ := by
    change some (TM2.stepAux (P (labels .skipPredicate)) _ _) = _
    rw [atStatement .skipPredicate]
    have h := congrArg some (stepAux_skipBits source row.relation.toList
      (.goto fun _ => labels .guard) base suffix ambient none)
    simpa only [statement, Vector.length_toList, relationWords, TM2.stepAux] using h
  rw [rowBits_eq]
  simp only [List.append_assoc]
  rw [show row.tail.val + row.reverseIndex.val + 3 =
    1 + ((row.reverseIndex.val + 1) + (row.tail.val + 1)) by omega,
    Function.iterate_add_apply, Function.iterate_add_apply, ht, hr,
    Function.iterate_one, advance_some, hp]

theorem skipRowTrace_fromTapes (base : K → List Bool) (row : DartRow q n m)
    (suffix : List Bool) (hinput : base source = rowBits row ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[row.tail.val + row.reverseIndex.val + 3]
      (some ⟨some (labels .skipTail), (ambient, register), base⟩) =
      some ⟨some (labels .guard), (ambient, none), Function.update base source suffix⟩ := by
  have h := skipRowTrace counter source destination labels exit P atStatement
    base row suffix ambient register
  have hb : Function.update base source (rowBits row ++ suffix) = base := by
    rw [← hinput]
    exact Function.update_eq_self source base
  rw [hb] at h
  exact h

theorem selectTrace (hsd : source ≠ destination) (base : K → List Bool)
    (row : DartRow q n m) (suffix : List Bool)
    (hinput : base source = rowBits row ++ suffix) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[row.tail.val + 2]
      (some ⟨some (labels .select), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), Hastad.SourceMachine.fieldTapes source destination base
        (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
        (encodeWord row.tail.val ++ base destination)⟩ := by
  let ht := Hastad.SourceMachine.fieldInTime source destination hsd
    (labels .select) (labels .copy) exit P (atStatement .select) (atStatement .copy)
    base row.tail.val
    (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
    (by simpa only [rowBits_eq, List.append_assoc] using hinput) ambient register
  have hsteps : ht.steps = row.tail.val + 2 := rfl
  have htrace := ht.evals_in_steps
  rw [hsteps] at htrace
  exact htrace

/-- Exact successful row lookup. The only data premise is the literal table
prefix; no lookup result or whole execution is postulated. -/
theorem lookupTailTrace
    (hcs : counter ≠ source) (hcd : counter ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (prior : List (DartRow q n m)) (row : DartRow q n m)
    (counterSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[lookupCost prior row]
      (some ⟨some (labels .guard), (ambient, register),
        MachineLookup.tapes counter source destination base
          (encodeWord prior.length ++ counterSuffix)
          (rowsBits prior ++ (rowBits row ++ suffix)) output⟩) =
      some ⟨exit, (ambient, none),
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix)
          (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
          (encodeWord row.tail.val ++ output)⟩ := by
  induction prior generalizing register with
  | nil =>
    simp only [lookupCost, prefixCost, List.map_nil, List.sum_nil, Nat.zero_add,
      List.length_nil, rowsBits_nil, List.nil_append]
    rw [show row.tail.val + 3 = (row.tail.val + 2) + 1 by omega,
      Function.iterate_succ_apply]
    have hg := MachineUnaryCounter.guardStep_zero counter (labels .guard)
      (labels .skipTail) (labels .select) P (atStatement .guard)
      (MachineLookup.tapes counter source destination base
        (encodeWord 0 ++ counterSuffix) (rowBits row ++ suffix) output)
      counterSuffix ambient register
    have hcounter : MachineUnaryCounter.counterTapes counter
        (MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix) (rowBits row ++ suffix) output) 0 counterSuffix =
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix) (rowBits row ++ suffix) output := by
      simp only [MachineUnaryCounter.counterTapes, MachineLookup.update_index _ _ _ hcs hcd]
    rw [hcounter] at hg
    simp only [advance_some]
    rw [hg]
    have hs := selectTrace counter source destination labels exit P atStatement hsd
      (MachineLookup.tapes counter source destination base
        (encodeWord 0 ++ counterSuffix) (rowBits row ++ suffix) output)
      row suffix (by simp [hsd]) ambient none
    simpa only [MachineLookup.tapes_destination,
      MachineLookup.fieldTapes_eq _ _ _ hsd] using hs
  | cons first prior ih =>
    simp only [lookupCost, prefixCost, List.map_cons, List.sum_cons, List.length_cons,
      rowsBits_cons, List.append_assoc]
    rw [show skipCost first + (prior.map skipCost).sum + row.tail.val + 3 =
      ((prior.map skipCost).sum + row.tail.val + 3) +
        (first.tail.val + first.reverseIndex.val + 3) + 1 by simp only [skipCost]; omega,
      Function.iterate_succ_apply]
    have hg := MachineUnaryCounter.guardStep_succ counter (labels .guard)
      (labels .skipTail) (labels .select) P (atStatement .guard)
      (MachineLookup.tapes counter source destination base
        (encodeWord prior.length ++ counterSuffix)
        (rowBits first ++ (rowsBits prior ++ (rowBits row ++ suffix))) output)
      prior.length counterSuffix ambient register
    simp only [MachineUnaryCounter.counterTapes,
      MachineLookup.update_index _ _ _ hcs hcd] at hg
    simp only [advance_some]
    rw [hg, Function.iterate_add_apply]
    have hs := skipRowTrace_fromTapes counter source destination labels exit P atStatement
      (MachineLookup.tapes counter source destination base
        (encodeWord prior.length ++ counterSuffix)
        (rowBits first ++ (rowsBits prior ++ (rowBits row ++ suffix))) output)
      first (rowsBits prior ++ (rowBits row ++ suffix)) (by simp [hsd]) ambient none
    rw [hs]
    simp only [MachineLookup.update_source _ _ _ hsd]
    exact ih none

end Ambient

/-- The number of actual transitions is linear in the scanned encoding and
the unary row index. Fixed predicate statements contribute one transition. -/
theorem lookupCost_le {q n m : Nat} (prior : List (DartRow q n m)) (row : DartRow q n m) :
    lookupCost prior row ≤ (rowsBits prior ++ rowBits row).length +
      2 * (encodeWord prior.length).length + 1 := by
  have hp : prefixCost prior ≤ (rowsBits prior).length + 2 * prior.length := by
    induction prior with
    | nil => simp [prefixCost]
    | cons first prior ih =>
      have hb : skipCost first ≤ (rowBits first).length + 2 := by
        simp only [skipCost, rowBits_eq, List.length_append, encodeWord_length]
        omega
      simp only [prefixCost, List.map_cons, List.sum_cons, rowsBits_cons,
        List.length_append, List.length_cons] at *
      omega
  have hr : row.tail.val + 1 ≤ (rowBits row).length := by
    simp only [rowBits_eq, List.length_append, encodeWord_length]
    omega
  simp only [lookupCost, List.length_append, encodeWord_length]
  omega

/-- The input's actual stored row vector determines the selected row. This
specialization derives the literal lookup prefix from the checked codec. -/
theorem tableTailTrace {q : Nat}
    (counter source destination : K) (labels : Label → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStatement : ∀ label, P (labels label) = statement q counter source destination labels exit label)
    (hcs : counter ≠ source) (hcd : counter ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (table : Table q) (e : Fin table.darts)
    (counterSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[lookupCost ((rowList table).take e.val) table.rows[e]]
      (some ⟨some (labels .guard), (ambient, register),
        MachineLookup.tapes counter source destination base
          (encodeWord e.val ++ counterSuffix) (rowsBits (rowList table) ++ suffix) output⟩) =
      some ⟨exit, (ambient, none),
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix)
          (encodeWord table.rows[e].reverseIndex.val ++
            (encodeWords (relationWords table.rows[e].relation) ++
              (rowsBits ((rowList table).drop (e.val + 1)) ++ suffix)))
          (encodeWord table.rows[e].tail.val ++ output)⟩ := by
  have h := lookupTailTrace counter source destination labels exit P atStatement
    hcs hcd hsd base ((rowList table).take e.val) table.rows[e] counterSuffix
    (rowsBits ((rowList table).drop (e.val + 1)) ++ suffix) output ambient register
  have hlength : ((rowList table).take e.val).length = e.val := by
    simp only [List.length_take, rowList_length, Nat.min_eq_left (Nat.le_of_lt e.isLt)]
  have hsplit : rowsBits (rowList table) ++ suffix =
      rowsBits ((rowList table).take e.val) ++
        (rowBits table.rows[e] ++ (rowsBits ((rowList table).drop (e.val + 1)) ++ suffix)) := by
    have hrow : table.rows[e.val] = table.rows[e] := rfl
    simpa only [rowsBits, rowBits, rowList, Vector.getElem_toList, hrow] using
      Input.rowsBits_append_split (rowList table) e.val (by simp) suffix
  rw [hlength, ← hsplit] at h
  exact h

/-- Two real delimiter-scanning loops remove the header of the copied table
before the row counter starts. The protected original table can occupy any
other tape in `base` and is unchanged. -/
theorem fullTableTailTrace {q : Nat}
    (counter source destination : K) (labels : Label → Λ) (exit : Option Λ)
    (headerVertices headerDarts : Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStatement : ∀ label, P (labels label) = statement q counter source destination labels exit label)
    (atVertices : P headerVertices = MachineLookup.discard source headerVertices headerDarts)
    (atDarts : P headerDarts = MachineLookup.discard source headerDarts (labels .guard))
    (hcs : counter ≠ source) (hcd : counter ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (table : Table q) (e : Fin table.darts)
    (counterSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[lookupCost ((rowList table).take e.val) table.rows[e] +
        (table.darts + 1) + (table.vertices + 1)]
      (some ⟨some headerVertices, (ambient, register),
        MachineLookup.tapes counter source destination base
          (encodeWord e.val ++ counterSuffix) (tableBits table ++ suffix) output⟩) =
      some ⟨exit, (ambient, none),
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix)
          (encodeWord table.rows[e].reverseIndex.val ++
            (encodeWords (relationWords table.rows[e].relation) ++
              (rowsBits ((rowList table).drop (e.val + 1)) ++ suffix)))
          (encodeWord table.rows[e].tail.val ++ output)⟩ := by
  have hv := MachineLookup.discardTrace source headerVertices headerDarts P atVertices
    (MachineLookup.tapes counter source destination base
      (encodeWord e.val ++ counterSuffix) (tableBits table ++ suffix) output)
    table.vertices (encodeWord table.darts ++ (rowsBits (rowList table) ++ suffix))
    (by simp only [MachineLookup.tapes_source _ _ _ hsd, Input.tableBits_header,
      rowsBits, List.append_assoc]) ambient register
  rw [Function.iterate_add_apply, hv]
  simp only [MachineLookup.update_source _ _ _ hsd]
  have hd := MachineLookup.discardTrace source headerDarts (labels .guard) P atDarts
    (MachineLookup.tapes counter source destination base
      (encodeWord e.val ++ counterSuffix)
      (encodeWord table.darts ++ (rowsBits (rowList table) ++ suffix)) output)
    table.darts (rowsBits (rowList table) ++ suffix) (by simp [hsd]) ambient none
  rw [Function.iterate_add_apply, hd]
  simp only [MachineLookup.update_source _ _ _ hsd]
  exact tableTailTrace counter source destination labels exit P atStatement hcs hcd hsd
    base table e counterSuffix suffix output ambient none

def tableTailCost {q : Nat} (table : Table q) (e : Fin table.darts) : Nat :=
  lookupCost ((rowList table).take e.val) table.rows[e] +
    (table.darts + 1) + (table.vertices + 1)

theorem tableTailCost_le {q : Nat} (table : Table q) (e : Fin table.darts) :
    tableTailCost table e ≤ (tableBits table).length + 2 * (encodeWord e.val).length + 1 := by
  have htake : ((rowList table).take e.val).length = e.val := by
    simp only [List.length_take, rowList_length, Nat.min_eq_left (Nat.le_of_lt e.isLt)]
  have hrow : table.rows[e.val] = table.rows[e] := rfl
  have hsplit : rowsBits (rowList table) = rowsBits ((rowList table).take e.val) ++
      (rowBits table.rows[e] ++ rowsBits ((rowList table).drop (e.val + 1))) := by
    simpa only [rowsBits, rowBits, rowList, Vector.getElem_toList, hrow] using
      Input.rowsBits_split (rowList table) e.val (by simp)
  have hp : (rowsBits ((rowList table).take e.val) ++ rowBits table.rows[e]).length ≤
      (rowsBits (rowList table)).length := by
    rw [hsplit]
    simp only [List.length_append]
    omega
  have hb := lookupCost_le ((rowList table).take e.val) table.rows[e]
  rw [htake] at hb
  have hh := congrArg List.length (Input.tableBits_header table)
  change (tableBits table).length =
    (encodeWord table.vertices ++ (encodeWord table.darts ++ rowsBits (rowList table))).length at hh
  simp only [List.length_append, encodeWord_length] at hh
  unfold tableTailCost
  omega

end MaxCutGames.Foundations.PCP.AlphabetTable.Lookup

/-!
The finite registers and physical tape roles of the alphabet-table machine.
Input-sized numbers occur only on unary tapes. The comparison and emitter
register layouts are related by explicit, executable product rearrangements.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_CompareLoop
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual finite TM2 templates for affine unary fields and finite relation bits.
Commands write in forward bit order onto a stack, so their concatenated result
appears reversed in the accumulator. Every unbounded operand is read from an
isolated unary tape and restored by the checked preserving transducer.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Emitter

open Turing
open MaxCutGames.Foundations.Complexity
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} {h bound : Nat} [DecidableEq K]

/-- Exact execution of one command of the supplied actual program. The only
program hypotheses are equations for its concrete finite statements. -/
theorem commandTrace (sources : Fin h → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Phase bound → Λ) (next : Λ) (command : Command h σ bound)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ phase,
      program (labels phase) = commandStatement sources scratch output labels next command phase)
    (values : Fin h → Nat) (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (values i))
    (scratchEmpty : base scratch = []) (ambient : σ) :
    (MachineComposition.advance (TM2.step program))^[commandSteps values command]
      (some ⟨some (labels .entry), ((ambient, ()), none), base⟩) =
      some ⟨some next, ((ambient, ()), none),
        Function.update base output ((commandBits values ambient command).reverse ++ base output)⟩ := by
  cases command with
  | literal word =>
    change some (TM2.stepAux (program (labels .entry)) ((ambient, ()), none) base) = _
    rw [atLabels]
    simp only [commandStatement, stepAux_pushWord, TM2.stepAux, commandBits]
  | bit value =>
    change some (TM2.stepAux (program (labels .entry)) ((ambient, ()), none) base) = _
    rw [atLabels]
    cases hb : value ambient <;>
      simp [commandStatement, TM2.stepAux, pushWord, commandBits, hb, encodeWord]
  | bounded value =>
    change (TM2.step program ⟨some (labels .entry), ((ambient, ()), none), base⟩).bind
      (TM2.step program) = _
    have first : TM2.step program ⟨some (labels .entry), ((ambient, ()), none), base⟩ =
        some ⟨some (labels (.offset (value ambient))), ((ambient, ()), none), base⟩ := by
      change some (TM2.stepAux (program (labels .entry)) _ _) = _
      rw [atLabels]
      rfl
    rw [first]
    change some (TM2.stepAux (program (labels (.offset (value ambient)))) _ _) = _
    rw [atLabels]
    simp only [commandStatement, stepAux_pushWord, TM2.stepAux, commandBits]
  | scaled source coefficient =>
    have emitAt : ∀ control symbol, program (labels (.emit symbol)) =
        MachineTransducerCopy.emitter output transition (payload coefficient)
          (labels .entry) control symbol := by
      intro control symbol
      cases control
      exact atLabels (.emit symbol)
    have run := MachineTransducerCopy.transduceCopyTrace (sources source) scratch output
      (sourceScratch source) (sourceOutput source) scratchOutput () transition (payload coefficient)
      (labels .entry) (labels .restore) (fun _ symbol => labels (.emit symbol)) (some next)
      program (atLabels .entry) emitAt (atLabels .restore) base scratchEmpty ambient () none
    rw [operands source, encodeWord_length, output_encodeWord_inline_Emitter] at run
    exact run
  | scaledIf source coefficient active =>
    have first : TM2.step program ⟨some (labels .entry), ((ambient, ()), none), base⟩ =
        some ⟨some (labels (.scanIf (active ambient))), ((ambient, ()), none), base⟩ := by
      change some (TM2.stepAux (program (labels .entry)) _ _) = _
      rw [atLabels]
      rfl
    have emitAt : ∀ control symbol, program (labels (.emitIf (active ambient) symbol)) =
        MachineTransducerCopy.emitter output transition
          (payload (if active ambient then coefficient else 0))
          (labels (.scanIf (active ambient))) control symbol := by
      intro control symbol
      cases control
      exact atLabels (.emitIf (active ambient) symbol)
    have run := MachineTransducerCopy.transduceCopyTrace (sources source) scratch output
      (sourceScratch source) (sourceOutput source) scratchOutput () transition
      (payload (if active ambient then coefficient else 0))
      (labels (.scanIf (active ambient))) (labels .restore)
      (fun _ symbol => labels (.emitIf (active ambient) symbol)) (some next)
      program (atLabels (.scanIf (active ambient))) emitAt (atLabels .restore)
      base scratchEmpty ambient () none
    rw [operands source, encodeWord_length, output_encodeWord_inline_Emitter] at run
    change (MachineComposition.advance (TM2.step program))^[
      (3 * (values source + 1) + 2) + 1] _ = _
    rw [Function.iterate_succ_apply]
    simp only [MachineComposition.advance_some]
    rw [first]
    exact run

/-- Composition of the actual finite command traces, with preserved operand
stacks available again at every command boundary. -/
theorem prefixTrace {count : Nat} (commands : Fin count → Command h σ bound)
    (sources : Fin h → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Label count bound → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement commands sources scratch output labels exit label)
    (values : Fin h → Nat) (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (values i))
    (scratchEmpty : base scratch = []) (ambient : σ) (r : Nat) (hr : r ≤ count) :
    (MachineComposition.advance (TM2.step p))^[prefixSteps commands values r]
      (some ⟨some (labels (labelAt count bound 0 .entry)), ((ambient, ()), none), base⟩) =
      some ⟨some (labels (labelAt count bound r .entry)), ((ambient, ()), none),
        resultTapes output base (prefixBits commands values ambient r)⟩ := by
  induction r with
  | zero => simp [prefixSteps, prefixBits, resultTapes]
  | succ r ih =>
    have hrc : r < count := by omega
    let prior := resultTapes output base (prefixBits commands values ambient r)
    have priorOperands : ∀ i, prior (sources i) = encodeWord (values i) := by
      intro i
      simpa [prior, resultTapes, sourceOutput i] using operands i
    have priorScratch : prior scratch = [] := by
      simpa [prior, resultTapes, scratchOutput] using scratchEmpty
    have commandAtLabels : ∀ phase, p (labels (labelAt count bound r phase)) =
        commandStatement sources scratch output (fun phase => labels (labelAt count bound r phase))
          (labels (labelAt count bound (r + 1) .entry)) (commandAt commands r) phase := by
      intro phase
      rw [atLabels]
      simp only [statement, labelAt, Nat.min_eq_left (Nat.le_of_lt hrc), hrc, ite_true, if_true]
    have one := commandTrace sources scratch output sourceScratch sourceOutput scratchOutput
      (fun phase => labels (labelAt count bound r phase))
      (labels (labelAt count bound (r + 1) .entry)) (commandAt commands r)
      p commandAtLabels values prior priorOperands priorScratch ambient
    rw [prefixSteps, Nat.add_comm, Function.iterate_add_apply, ih (by omega)]
    rw [one]
    congr 2
    simp [prior, prefixBits, resultTapes, List.reverse_append, List.append_assoc]

/-- The complete callable program, including its actual final jump or halt. -/
theorem planTrace {count : Nat} (commands : Fin count → Command h σ bound)
    (sources : Fin h → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Label count bound → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement commands sources scratch output labels exit label)
    (values : Fin h → Nat) (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (values i))
    (scratchEmpty : base scratch = []) (ambient : σ) :
    (MachineComposition.advance (TM2.step p))^[prefixSteps commands values count + 1]
      (some ⟨some (labels (labelAt count bound 0 .entry)), ((ambient, ()), none), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        resultTapes output base (prefixBits commands values ambient count)⟩ := by
  rw [Function.iterate_succ_apply', prefixTrace commands sources scratch output sourceScratch
    sourceOutput scratchOutput labels exit p atLabels values base operands scratchEmpty ambient count
    (Nat.le_refl _)]
  change some (TM2.stepAux (p (labels (labelAt count bound count .entry))) _ _) = _
  rw [atLabels]
  cases exit <;> simp [statement, labelAt, Reduction.MachineTransfer.exitAt, TM2.stepAux]

/-- A linear bound in the largest unary input field; plan size is fixed. -/
def planInTime {count : Nat} (commands : Fin count → Command h σ bound)
    (sources : Fin h → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Label count bound → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement commands sources scratch output labels exit label)
    (values : Fin h → Nat) (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (values i))
    (scratchEmpty : base scratch = []) (ambient : σ)
    (N : Nat) (bounded : ∀ i, values i ≤ N) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (labelAt count bound 0 .entry)), ((ambient, ()), none), base⟩
      (some ⟨exit, ((ambient, ()), none),
        resultTapes output base (prefixBits commands values ambient count)⟩)
      (count * (3 * (N + 1) + 3) + 1) where
  steps := prefixSteps commands values count + 1
  evals_in_steps := planTrace commands sources scratch output sourceScratch sourceOutput
    scratchOutput labels exit p atLabels values base operands scratchEmpty ambient
  steps_le_m := Nat.add_le_add_right (prefixSteps_le commands values N bounded count) 1

end MaxCutGames.Foundations.PCP.AlphabetTable.Emitter

/-!
# Affine numeric fields of the alphabet-reduction table

The five unbounded unary inputs are n, m, e, tail, head, in that order.
Every field uses a fixed list of natural coefficients and one bounded offset.
For a fixed local event and slot, the query field's coefficient list does not
depend on the input predicate. The predicate changes only its bounded offset.
Evaluation uses the same `Emitter.affineValue` as the actual unary emitter.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_GraphTableComplexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Concrete bridges between graph cardinality and the length of the validated
unary table encoding. These bounds supply the input-length and intermediate
encoding estimates used by actual machine trace composition; they are not
themselves a machine execution certificate.
-/

namespace MaxCutGames.Foundations.PCP.GraphTableComplexity

open MaxCutGames.Foundations.Complexity
open Polynomial

theorem size_add_two_le_bits (table : GraphTables.Table) :
    table.vertices + table.darts + 2 ≤ (GraphTables.tableBits table).length := by
  simp only [GraphTables.tableBits, GraphTables.tableWords,
    encodeWords_append, List.length_append, encodeWords, encodeWord_length, List.length_nil]
  omega

theorem bits_le_polynomial (table : GraphTables.Table) :
    (GraphTables.tableBits table).length ≤
      (encodingPolynomial 64).eval (table.vertices + table.darts) :=
  (GraphTables.tableBits_length_le table).trans
    (rowBound_le_polynomial 64 table.vertices table.darts)

theorem bits_le_of_size_le {N : Nat} (table : GraphTables.Table)
    (hsize : table.vertices + table.darts ≤ N) :
    (GraphTables.tableBits table).length ≤ (encodingPolynomial 64).eval N :=
  (bits_le_polynomial table).trans (encodingPolynomial_mono 64 hsize)

end MaxCutGames.Foundations.PCP.GraphTableComplexity

/-!
The actual fixed-parameter graph transformation in one PCP amplification round.
It preprocesses the input graph, checks all edges of each bounded walk using
local endpoint labels, and applies the checked constant-query alphabet reduction.
The bounded address list is explicit fixed data shared by every input graph.
-/

/-!
# The actual first moment of an endpoint-opinion witness

The pivot factorization is applied to actual finite walks. Its two endpoint
operator bounds are obtained from the proved lazy-graph mixture and smoothing
theorem. No witness-event probability law is assumed.
-/

/-! The second moment of the actual marked-edge count in a consecutive walk
window. Pair events are reduced to the checked spectral return operator. -/

/-!
# The scalar bound for all positive error densities

The first lemma bounds a ratio using only a nonnegative coefficient bounded
by a positive cutoff. The second applies it to a positive natural count and
the first- and second-moment expressions in the powering argument.
-/

/-! The actual graph-powering soundness bound. Modal endpoint opinions give
the first moment, spectral return gives the second moment, and an actual
checked path constraint turns each witness into rejection. -/

/-!
# The fixed constants in the actual powering estimate

The six-bit alphabet has 64 letters. The middle window, endpoint length,
spectral parameter and composition loss in the checked powering theorem give
exactly the constants used in the final amplification round. Large natural
constants remain symbolic in these calculations.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_RawInitialMachineCleanup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual cleanup of all six clause-field tapes followed by the global unary
index increment. The output accumulator, unread input, and other caller tapes
are preserved, and no additional finish instruction is assumed.
-/

/-! One complete clause iteration of the actual initial graph machine. -/

/-! Exact execution of the dummy-row and final cleanup/reversal phases. -/

/-! Exact execution of the clause loop, in the original occurrence order. -/

/-! The actual finite machine computing the initial graph's full serialized
table. The runtime bound counts every parse, row, cleanup and output reversal. -/

/-!
Actual finite-machine phases for the final twelve-query verifier conversion.
The graph codec stores a relation bit as the unary natural 0 or 1. The reader
below consumes those variable-length codewords, rather than treating the row
as an already available raw Boolean block. Its finite register size is fixed
at 4096 for the final alphabet, independent of the graph input size.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine

open Turing
open PCP

namespace Program

open PCP.AlphabetTable

/-- Output variable count and output clause count, in the checked CNF codec. -/
def headerPlan : Plan :=
  Emitter.affineCommands [(0, 6), (1, 36864)] (fun _ => 0) ++
    Emitter.affineCommands [(1, 40960)] (fun _ => 0)

theorem headerPlan_length : headerPlan.length = 7 := by
  simp [headerPlan]

/-- The actual finite program. All graph-dependent naturals remain on unary
stacks. The only buffered graph data is one fixed 4096-bit relation table. -/
def program (headerPlan rowPlan : Plan) :
    Label headerPlan.length rowPlan.length →
      TM2.Stmt (fun _ : Tape => Bool) (Label headerPlan.length rowPlan.length) (State Unit)
  | .copyFirst => Reduction.MachineTransfer.loopAt .input .scratch id false .copyFirst
      (some .copySecond)
  | .copySecond => MachineCopy.forkLoop .scratch .input .archive false .copySecond
      (some .startVertices)
  | .startVertices => Hastad.SourceMachine.fieldStart .vertices .readVertices
  | .readVertices => Hastad.SourceMachine.fieldLoop .input .vertices .readVertices (some .startDarts)
  | .startDarts => Hastad.SourceMachine.fieldStart .darts .readDarts
  | .readDarts => Hastad.SourceMachine.fieldLoop .input .darts .readDarts (some .seedIndex)
  | .seedIndex => .push .rowIndex (fun _ => false)
      (.push .tail (fun _ => false) (.push .head (fun _ => false)
        (.goto fun _ => .header (Emitter.labelAt headerPlan.length 36864 0 .entry))))
  | .header label => Emitter.statement (Emitter.listCommands headerPlan)
      source .scratch .accumulator Label.header (some .headerClearTail) label
  | .headerClearTail => MachineLookup.discard .tail .headerClearTail .headerClearHead
  | .headerClearHead => MachineLookup.discard .head .headerClearHead .guard
  | .guard => guard .startTail .reverseOutput
  | .startTail => Hastad.SourceMachine.fieldStart .tail .readTail
  | .readTail => Hastad.SourceMachine.fieldLoop .input .tail .readTail (some .startReverse)
  | .startReverse => Hastad.SourceMachine.fieldStart .reverseIndex .readReverse
  | .readReverse => Hastad.SourceMachine.fieldLoop .input .reverseIndex .readReverse
      (some .headTableFirst)
  | .headTableFirst => Reduction.MachineTransfer.loopAt .archive .scratch id false
      .headTableFirst (some .headTableSecond)
  | .headTableSecond => MachineCopy.forkLoop .scratch .archive .scanWork false
      .headTableSecond (some .headIndexFirst)
  | .headIndexFirst => Reduction.MachineTransfer.loopAt .reverseIndex .scratch id false
      .headIndexFirst (some .headIndexSecond)
  | .headIndexSecond => MachineCopy.forkLoop .scratch .reverseIndex .indexWork false
      .headIndexSecond (some .headHeaderVertices)
  | .headHeaderVertices => MachineLookup.discard .scanWork .headHeaderVertices .headHeaderDarts
  | .headHeaderDarts => MachineLookup.discard .scanWork .headHeaderDarts (.headLookup .guard)
  | .headLookup label => Lookup.statement 64 .indexWork .scanWork .head Label.headLookup
      (some .readRelation) label
  | .readRelation => readRelationAt .input
      (.row (Emitter.labelAt rowPlan.length 36864 0 .entry))
  | .row label => Emitter.statement (Emitter.listCommands rowPlan)
      source .scratch .accumulator Label.row (some .clearTail) label
  | .clearTail => MachineLookup.discard .tail .clearTail .clearHead
  | .clearHead => MachineLookup.discard .head .clearHead .clearReverse
  | .clearReverse => MachineLookup.discard .reverseIndex .clearReverse .nextRow
  | .nextRow => .push .rowIndex (fun _ => true) (.goto fun _ => .guard)
  | .reverseOutput => Reduction.MachineTransfer.loopAt .accumulator .output id false
      .reverseOutput none

def machine (headerPlan rowPlan : Plan) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label headerPlan.length rowPlan.length
  main := .copyFirst
  σ := State Unit
  initialState := ((((), fun _ => false), ()), none)
  m := program headerPlan rowPlan

end Program

end MaxCutGames.Foundations.Complexity.FinalCNFMachine

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_FinalCNFStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Exact row enumeration and input/output stream identities for the concrete
final-CNF machine. Rows occur in stored order, including repeated rows.
-/

/-! The actual bounded loop over every stored row of the final CNF converter. -/

/-!
The complete actual output-producing trace of the final CNF machine. Its
terminal configuration still contains private work tapes before the
canonical halt required by the machine interface.
-/

/-!
Fixed literal templates for the twelve-query converter. All control data have
constant size: twelve query references, nine auxiliary references, ten clauses,
and three literal slots. Pattern bits remain symbolic throughout the proof.

These templates specify the actual serialized rows. Their machine execution
is proved separately in FinalCNFRow and FinalCNFComputation.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFTemplate

open Target PCP

variable (V : VerifierToCNF.FiniteVerifier 12) (e : Fin V.events)
  (p : VerifierToCNF.PatternIndex 12)

def resolve : Reference → Fin (VerifierToCNF.outputVariables V)
  | .query i => VerifierToCNF.oldIndex V (V.query e i)
  | .auxiliary j => VerifierToCNF.freshIndex V e p j

theorem resolve_query_value (i : Fin 12) :
    (resolve V e p (.query i)).val = (V.query e i).val := by
  simp only [resolve, VerifierToCNF.oldIndex, Fin.val_castAdd]

theorem resolve_auxiliary_value (j : Fin 9) :
    (resolve V e p (.auxiliary j)).val =
      V.«variables» + ((e.val * 4096 + p.val) * 9 + j.val) := by
  change (VerifierToCNF.freshIndex V e p j).val = _
  exact (VerifierToCNF.freshIndex_value V e p j).trans
    (congrArg (fun k : Nat => V.«variables» + ((e.val * k + p.val) * 9 + j.val))
      (show (VerifierToCNF.patterns 12).length = 4096 from VerifierToCNF.patterns_length 12))

end MaxCutGames.Foundations.Complexity.FinalCNFTemplate

/-!
The fixed finite emission plan for one directed graph row. All choices based
on the relation are functions of its 4096-bit finite register. Vertex counts,
endpoint names and row indices are read by preserving unary scans.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable FinalCNFTemplate

def referenceValue (vertices tail head row pattern : Nat) : Reference → Nat
  | .query i => if i.val < 6 then 6 * tail + i.val else 6 * head + (i.val - 6)
  | .auxiliary j => 6 * vertices + 36864 * row + (9 * pattern + j.val)

def auxiliaryFlag : Reference → Bool
  | .query _ => false
  | .auxiliary _ => true

def tailFlag : Reference → Bool
  | .query i => decide (i.val < 6)
  | .auxiliary _ => false

def headFlag : Reference → Bool
  | .query i => decide (6 ≤ i.val)
  | .auxiliary _ => false

theorem pattern_lt (p : VerifierToCNF.PatternIndex 12) : p.val < 4096 := by
  have hlen : (VerifierToCNF.patterns 12).length = 4096 := VerifierToCNF.patterns_length 12
  exact lt_of_lt_of_eq p.isLt hlen

def referenceOffset (p : VerifierToCNF.PatternIndex 12) : Reference → Fin 36864
  | .query i => ⟨if i.val < 6 then i.val else i.val - 6, by split <;> omega⟩
  | .auxiliary j => ⟨9 * p.val + j.val, by have hp := pattern_lt p; omega⟩

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineCloudCount
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineCeilingPower

open Turing
open MachineComposition
open MaxCutGames.Foundations.PCP

variable {σ : Type}

theorem compareStep_zero (g p : Nat) (input saved level fuel spare product : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .compare, ((ambient, flag), register),
        memory input (encodeWord 0) (encodeWord p) saved level fuel spare product⟩ =
      some ⟨some .restore, ((ambient, flag), none),
        memory input [] (encodeWord p) saved level fuel spare product⟩ := by
  change some (TM2.stepAux compareLoop _ _) = _
  simp [compareLoop, TM2.stepAux, memory, encodeWord]

theorem compareStep_succ_zero (g x : Nat) (input saved level fuel spare product : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .compare, ((ambient, flag), register),
        memory input (encodeWord (x + 1)) (encodeWord 0) saved level fuel spare product⟩ =
      some ⟨some .compare, ((ambient, true), none),
        memory input (encodeWord x) (encodeWord 0) saved level fuel spare product⟩ := by
  change some (TM2.stepAux compareLoop _ _) = _
  simp [compareLoop, TM2.stepAux, memory, encodeWord, List.replicate_succ]

theorem compareStep_succ_succ (g x p : Nat) (input saved level fuel spare product : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .compare, ((ambient, flag), register),
        memory input (encodeWord (x + 1)) (encodeWord (p + 1)) saved level fuel spare product⟩ =
      some ⟨some .compare, ((ambient, flag), none),
        memory input (encodeWord x) (encodeWord p) (true :: saved) level fuel spare product⟩ := by
  change some (TM2.stepAux compareLoop _ _) = _
  simp [compareLoop, TM2.stepAux, memory, encodeWord, List.replicate_succ]

/-- The comparison is performed by actual finite-head transitions. -/
theorem compareTrace (g x p : Nat) (input saved level fuel spare product : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step (program g)))^[x + 1]
      (some ⟨some .compare, ((ambient, flag), register),
        memory input (encodeWord x) (encodeWord p) saved level fuel spare product⟩) =
      some ⟨some .restore, ((ambient, overflow flag x p), none),
        memory input [] (encodeWord (p - x))
          (List.replicate (min x p) true ++ saved) level fuel spare product⟩ := by
  induction x generalizing p saved flag register with
  | zero =>
      simpa [overflow] using compareStep_zero g p input saved level fuel spare product ambient flag register
  | succ x ih =>
      rw [Function.iterate_succ_apply]
      change (advance (TM2.step (program g)))^[x + 1]
        (TM2.step (program g) ⟨some .compare, ((ambient, flag), register),
          memory input (encodeWord (x + 1)) (encodeWord p) saved level fuel spare product⟩) = _
      cases p with
      | zero =>
          rw [compareStep_succ_zero]
          simpa [overflow] using ih 0 saved true none
      | succ p =>
          rw [compareStep_succ_succ]
          simpa [overflow, Nat.succ_min_succ, List.replicate_succ', List.append_assoc] using
            ih p (true :: saved) flag none

theorem compareRestoredTrace (g k p : Nat) (level fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[k + min k p + 2]
      (some ⟨some .compare, ((ambient, false), register),
        memory (encodeWord k) (encodeWord k) (encodeWord p) [] level fuel [] []⟩) =
      some ⟨some .decide, ((ambient, decide (p < k)), none),
        memory (encodeWord k) [] (encodeWord p) [] level fuel [] []⟩ := by
  have hc := compareTrace g k p (encodeWord k) [] level fuel [] [] ambient false register
  simp only [overflow, Bool.false_or, List.append_nil] at hc
  let mid := memory (encodeWord k) [] (encodeWord (p - k))
    (List.replicate (min k p) true) level fuel [] []
  have hr := Reduction.MachineTransfer.transferAt_fromTapes Tape.saved Tape.power (by decide)
    id false Label.restore (some Label.decide) (program g) rfl mid (ambient, decide (p < k)) none
  have hsum : min k p + (p - k) = p := by omega
  simp only [mid, memory, List.length_replicate, List.reverse_replicate, List.map_id,
    Reduction.MachineTransfer.tapesAt, update_saved, update_power] at hr
  rw [replicate_encodeWord, hsum] at hr
  rw [show k + min k p + 2 = (min k p + 1) + (k + 1) by omega,
    Function.iterate_add_apply, hc]
  exact hr

theorem scaleStep_succ (g p b : Nat) (input level fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .scale, ((ambient, false), register),
        memory input [] (encodeWord (p + 1)) [] level fuel [] (List.replicate b true)⟩ =
      some ⟨some .scale, ((ambient, false), some true),
        memory input [] (encodeWord p) [] level fuel [] (List.replicate (g + b) true)⟩ := by
  change some (TM2.stepAux (scaleLoop g) _ _) = _
  simp [scaleLoop, TM2.stepAux, memory, encodeWord, List.replicate_succ,
    Reduction.MachineSubstitution.stepAux_pushWord]

theorem scaleStep_zero (g b : Nat) (input level fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .scale, ((ambient, false), register),
        memory input [] (encodeWord 0) [] level fuel [] (List.replicate b true)⟩ =
      some ⟨some .transfer, ((ambient, false), none),
        memory input [] (encodeWord 0) [] (true :: level) fuel [] (List.replicate b true)⟩ := by
  change some (TM2.stepAux (scaleLoop g) _ _) = _
  simp [scaleLoop, TM2.stepAux, memory, encodeWord]

theorem scaleScanTrace (g p b : Nat) (input level fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[p + 1]
      (some ⟨some .scale, ((ambient, false), register),
        memory input [] (encodeWord p) [] level fuel [] (List.replicate b true)⟩) =
      some ⟨some .transfer, ((ambient, false), none),
        memory input [] (encodeWord 0) [] (true :: level) fuel [] (List.replicate (g * p + b) true)⟩ := by
  induction p generalizing b register with
  | zero => simpa using scaleStep_zero g b input level fuel ambient register
  | succ p ih =>
      rw [Function.iterate_succ_apply]
      change (advance (TM2.step (program g)))^[p + 1]
        (TM2.step (program g) ⟨some .scale, ((ambient, false), register),
          memory input [] (encodeWord (p + 1)) [] level fuel [] (List.replicate b true)⟩) = _
      rw [scaleStep_succ, ih]
      have h : g * p + (g + b) = g * (p + 1) + b := by rw [Nat.mul_succ]; omega
      rw [h]

/-- The fixed-coefficient unary multiplication is an actual scan and transfer;
the level increment is one explicit push in the final scan transition. -/
theorem scaleTrace (g k p e : Nat) (fuel : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[p + g * p + 2]
      (some ⟨some .scale, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) fuel [] []⟩) =
      some ⟨some .guard, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord (p * g)) [] (encodeWord (e + 1)) fuel [] []⟩ := by
  have hs := scaleScanTrace g p 0 (encodeWord k) (encodeWord e) fuel ambient register
  simp only [List.replicate_zero, Nat.add_zero] at hs
  let mid := memory (encodeWord k) [] (encodeWord 0) [] (true :: encodeWord e) fuel []
    (List.replicate (g * p) true)
  have ht := Reduction.MachineTransfer.transferAt_fromTapes Tape.product Tape.power (by decide)
    id false Label.transfer (some Label.guard) (program g) rfl mid (ambient, false) none
  simp only [mid, memory, List.length_replicate, List.reverse_replicate, List.map_id,
    Reduction.MachineTransfer.tapesAt, update_product, update_power,
    replicate_encodeWord, Nat.add_zero] at ht
  have he : true :: encodeWord e = encodeWord (e + 1) := by simp [encodeWord, List.replicate_succ]
  rw [he, Nat.mul_comm g p] at ht
  rw [he, Nat.mul_comm g p] at hs
  have h := appendTrace_inline_MachineCeilingPower (advance (TM2.step (program g))) hs ht
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm] using h

theorem cleanupTrace (g k p e f : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[f + 2]
      (some ⟨some .cleanup, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) [] [] []⟩ := by
  have h := MachineDrain.drainTrace Tape.fuel Label.cleanup none (program g) rfl
    (memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) [] [] [])
    (encodeWord f) (ambient, false) register
  simpa only [encodeWord_length, update_fuel, Nat.add_assoc] using h

theorem guardStep_succ (g k p e f : Nat) (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord (f + 1)) [] []⟩ =
      some ⟨some .copyFirst, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ := by
  have h := MachineUnaryCounter.guardStep_succ Tape.fuel Label.guard Label.copyFirst Label.cleanup
    (program g) rfl (memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) [] [] [])
    f [] (ambient, false) register
  simpa only [MachineUnaryCounter.counterTapes, List.append_nil, update_fuel] using h

theorem guardStep_zero (g k p e : Nat) (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord 0) [] []⟩ =
      some ⟨some .cleanup, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord 0) [] []⟩ := by
  have h := MachineUnaryCounter.guardStep_zero Tape.fuel Label.guard Label.copyFirst Label.cleanup
    (program g) rfl (memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) [] [] [])
    [] (ambient, false) register
  simpa only [MachineUnaryCounter.counterTapes, List.append_nil, update_fuel] using h

theorem decideStep (g k p e f : Nat) (ambient : σ) :
    TM2.step (program g)
      ⟨some .decide, ((ambient, decide (p < k)), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ =
      some ⟨some (if k ≤ p then Label.cleanup else Label.scale), ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ := by
  by_cases h : k ≤ p
  · have hn : ¬p < k := by omega
    simp [TM2.step, program, TM2.stepAux, h, hn]
  · have hn : p < k := by omega
    simp [TM2.step, program, TM2.stepAux, h, hn]

/-- The loop prefix is an actual guard, preserving copy, comparison,
restoration and finite decision, all in the same fixed program. -/
theorem prefixTrace (g k p e f : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[prefixTime k p]
      (some ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord (f + 1)) [] []⟩) =
      some ⟨some (if k ≤ p then Label.cleanup else Label.scale), ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ := by
  have hg : (advance (TM2.step (program g)))^[1]
      (some ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord (f + 1)) [] []⟩) =
      some ⟨some .copyFirst, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ :=
    guardStep_succ g k p e f ambient register
  have hc := MachineCopy.copyTrace Tape.input Tape.work Tape.spare
    (by decide) (by decide) (by decide) false Label.copyFirst Label.copySecond
    (some Label.compare) (program g) rfl rfl
    (memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] [])
    rfl (ambient, false) none
  simp only [memory, encodeWord_length, List.append_nil, update_work] at hc
  have hcmp := compareRestoredTrace g k p (encodeWord e) (encodeWord f) ambient none
  have hd : (advance (TM2.step (program g)))^[1]
      (some ⟨some .decide, ((ambient, decide (p < k)), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩) =
      some ⟨some (if k ≤ p then Label.cleanup else Label.scale), ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩ :=
    decideStep g k p e f ambient
  exact appendTrace_inline_MachineCeilingPower _ (appendTrace_inline_MachineCeilingPower _ (appendTrace_inline_MachineCeilingPower _ hg hc) hcmp) hd

/-- The fixed machine realizes the exact previously checked bounded loop.
Every initial fuel tally is either used or cleared before halting. -/
theorem coreTrace (g k f e p : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[coreTime g k f p]
      (some ⟨some .guard, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord f) [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (encodeWord k) []
          (encodeWord (PreprocessingLevels.levelLoop g k f e p).2) []
          (encodeWord (PreprocessingLevels.levelLoop g k f e p).1) [] [] []⟩ := by
  induction f generalizing e p register with
  | zero =>
      have hg : (advance (TM2.step (program g)))^[1]
          (some ⟨some .guard, ((ambient, false), register),
            memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord 0) [] []⟩) =
          some ⟨some .cleanup, ((ambient, false), none),
            memory (encodeWord k) [] (encodeWord p) [] (encodeWord e) (encodeWord 0) [] []⟩ :=
        guardStep_zero g k p e ambient register
      exact appendTrace_inline_MachineCeilingPower _ hg (cleanupTrace g k p e 0 ambient none)
  | succ f ih =>
      have hpref := prefixTrace g k p e f ambient register
      by_cases h : k ≤ p
      · simp only [h, ite_true, if_true] at hpref
        have hrun := appendTrace_inline_MachineCeilingPower _ hpref (cleanupTrace g k p e f ambient none)
        simpa only [coreTime, PreprocessingLevels.levelLoop, h, ite_true, if_true] using hrun
      · simp only [h, ite_false] at hpref
        have hscale := scaleTrace g k p e (encodeWord f) ambient none
        have hrun := appendTrace_inline_MachineCeilingPower _ hpref (appendTrace_inline_MachineCeilingPower _ hscale (ih (e + 1) (p * g) none))
        simpa only [coreTime, PreprocessingLevels.levelLoop, h, ite_false] using hrun

theorem initStep (g k : Nat) (ambient : σ) (register : Option Bool) :
    TM2.step (program g)
      ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩ =
      some ⟨some .fuelFirst, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord 1) [] (encodeWord 0) [] [] []⟩ := by
  change some (TM2.stepAux (program g .init) _ _) = _
  simp [program, TM2.stepAux, memory, encodeWord]

/-- Initialization writes one and zero, copies the actual input to the fuel
tape, and executes the proved loop. All auxiliary tapes are empty on exit. -/
theorem searchTrace (g k : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program g)))^[totalTime g k]
      (some ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (encodeWord k) []
          (encodeWord (PreprocessingLevels.levelLoop g k k 0 1).2) []
          (encodeWord (PreprocessingLevels.levelLoop g k k 0 1).1) [] [] []⟩ := by
  have hi : (advance (TM2.step (program g)))^[1]
      (some ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩) =
      some ⟨some .fuelFirst, ((ambient, false), register),
        memory (encodeWord k) [] (encodeWord 1) [] (encodeWord 0) [] [] []⟩ :=
    initStep g k ambient register
  have hc := MachineCopy.copyTrace Tape.input Tape.fuel Tape.spare
    (by decide) (by decide) (by decide) false Label.fuelFirst Label.fuelSecond
    (some Label.guard) (program g) rfl rfl
    (memory (encodeWord k) [] (encodeWord 1) [] (encodeWord 0) [] [] [])
    rfl (ambient, false) register
  simp only [memory, encodeWord_length, List.append_nil, update_fuel] at hc
  exact appendTrace_inline_MachineCeilingPower _ (appendTrace_inline_MachineCeilingPower _ hi hc) (coreTrace g k k 0 1 ambient none)

/-- Instantiate the fixed program with the actual expander growth. This is
the exact executable result already identified with the ceiling logarithm. -/
theorem paddingTrace (k : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program ExpanderFamily.growth)))^[totalTime ExpanderFamily.growth k]
      (some ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord (PreprocessingLevels.paddedSize k)) []
          (encodeWord (PreprocessingLevels.boundedLevel k)) [] [] []⟩ := by
  exact searchTrace ExpanderFamily.growth k ambient register

def paddingInTime (k : Nat) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program ExpanderFamily.growth))
      ⟨some .init, ((ambient, false), register), memory (encodeWord k) [] [] [] [] [] [] []⟩
      (some ⟨none, ((ambient, false), none),
        memory (encodeWord k) [] (encodeWord (PreprocessingLevels.paddedSize k)) []
          (encodeWord (PreprocessingLevels.boundedLevel k)) [] [] []⟩)
      ((timePolynomial ExpanderFamily.growth).eval (encodeWord k).length) where
  steps := totalTime ExpanderFamily.growth k
  evals_in_steps := paddingTrace k ambient register
  steps_le_m := by rw [timePolynomial_encoding]; exact totalTime_le _ _

theorem paddingOutput_bounds (k : Nat) :
    PreprocessingLevels.boundedLevel k ≤ k ∧
      k ≤ PreprocessingLevels.paddedSize k ∧
      PreprocessingLevels.paddedSize k ≤ ExpanderFamily.growth * (k + 1) := by
  refine ⟨PreprocessingLevels.boundedLevel_le_input k, PreprocessingLevels.le_paddedSize k, ?_⟩
  by_cases hk : k = 0
  · subst k
    simpa using ExpanderFamily.growth_gt_one.le
  · exact (PreprocessingLevels.paddedSize_bounds (Nat.pos_of_ne_zero hk)).2.trans
      (Nat.mul_le_mul_left ExpanderFamily.growth (Nat.le_succ k))

end MaxCutGames.Foundations.Complexity.MachineCeilingPower

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineCloudPadding
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual cloud counting, geometric padding, and unary subtraction

One finite program places the checked cloud counter and geometric search on
shared tapes. Its final phase physically subtracts the preserved cloud size
from the computed power. A head test handles the empty cloud separately.
-/

namespace MaxCutGames.Foundations.Complexity.MachineCloudPadding

open Turing
open MachineComposition
open MaxCutGames.Foundations.PCP

/- Static placement of homogeneous tapes, with an explicit finite partial
inverse. Complement tapes are preserved by every simulated transition. -/

variable {σ : Type}

def program : Label → TM2.Stmt Alphabet Label (State σ)
  | .init => .push .count (fun _ => false) (.goto fun _ => .countCode .copyFirst)
  | .countCode l => Placement.statement countTape Label.countCode (some .branch)
      (MachineCloudCount.program l)
  | .branch => .peek .count (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.load (fun state => (state.1, none)) (.goto fun _ => .powerCode .init))
        (.push .power (fun _ => false) (.push .level (fun _ => false)
          (.load (fun state => (state.1, none)) .halt))))
  | .powerCode l => Placement.statement powerTape Label.powerCode (some .subtract)
      (MachineCeilingPower.program ExpanderFamily.growth l)
  | .subtract => subtractLoop
  | .restore => Reduction.MachineTransfer.loopAt
      .scratch .count id false .restore none

theorem countTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineCloudCount.totalSteps t.vertices t.darts v.val
      (MachineCloudCount.tableRows t)]
      (some ⟨some (.countCode .copyFirst), ((ambient, false), register),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix)
          (encodeWord 0) [] [] [] [] [] [] []⟩) =
      some ⟨some .branch, ((ambient, false), none),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix)
          (encodeWord (PreprocessingCloudIndex.cloudSize t v)) [] [] [] [] [] [] []⟩ := by
  have h := Placement.trace countTape countView countView_left countView_right
    Label.countCode (some Label.branch) (fun _ => [])
    (MachineCloudCount.program (σ := σ)) program (fun _ => rfl) _ _ _
    (MachineCloudCount.cloudCountTrace t v suffix [] ambient register)
  simpa only [Placement.configuration, Placement.label, countTapes, List.append_nil] using h

theorem powerTrace (table query : List Bool) (k : Nat) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step program))^[MachineCeilingPower.totalTime ExpanderFamily.growth k]
      (some ⟨some (.powerCode .init), ((ambient, false), register),
        memory table query (encodeWord k) [] [] [] [] [] [] []⟩) =
      some ⟨some .subtract, ((ambient, false), none),
        memory table query (encodeWord k) [] [] []
          (encodeWord (PreprocessingLevels.paddedSize k))
          (encodeWord (PreprocessingLevels.boundedLevel k)) [] []⟩ := by
  have h := Placement.trace powerTape powerView powerView_left powerView_right
    Label.powerCode (some Label.subtract) (memory table query [] [] [] [] [] [] [] [])
    (MachineCeilingPower.program ExpanderFamily.growth (σ := σ)) program (fun _ => rfl)
    _ _ _ (MachineCeilingPower.paddingTrace k ambient register)
  simpa only [Placement.configuration, Placement.label, powerTapes, memory] using h

theorem subtractStep_zero (table query level saved : List Bool) (p : Nat)
    (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some .subtract, ((ambient, false), register),
        memory table query (encodeWord 0) [] saved [] (encodeWord p) level [] []⟩ =
      some ⟨some .restore, ((ambient, false), none),
        memory table query (encodeWord 0) [] saved [] (encodeWord p) level [] []⟩ := by
  change some (TM2.stepAux subtractLoop _ _) = _
  simp [subtractLoop, TM2.stepAux, memory, encodeWord]

theorem subtractStep_succ (table query level saved : List Bool) (k p : Nat)
    (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some .subtract, ((ambient, false), register),
        memory table query (encodeWord (k + 1)) [] saved [] (encodeWord (p + 1)) level [] []⟩ =
      some ⟨some .subtract, ((ambient, false), none),
        memory table query (encodeWord k) [] (true :: saved) [] (encodeWord p) level [] []⟩ := by
  change some (TM2.stepAux subtractLoop _ _) = _
  simp [subtractLoop, TM2.stepAux, memory, encodeWord, List.replicate_succ]

theorem subtractScanTrace (table query level : List Bool) (k p : Nat)
    (saved : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[k + 1]
      (some ⟨some .subtract, ((ambient, false), register),
        memory table query (encodeWord k) [] saved [] (encodeWord (k + p)) level [] []⟩) =
      some ⟨some .restore, ((ambient, false), none),
        memory table query (encodeWord 0) [] (List.replicate k true ++ saved) []
          (encodeWord p) level [] []⟩ := by
  induction k generalizing saved register with
  | zero => simpa only [Nat.zero_add, Function.iterate_one, advance_some,
      List.replicate_zero, List.nil_append] using
      subtractStep_zero table query level saved p ambient register
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    simp only [Nat.succ_add]
    change (advance (TM2.step program))^[k + 1]
      (TM2.step program ⟨some .subtract, ((ambient, false), register),
        memory table query (encodeWord (k + 1)) [] saved []
          (encodeWord ((k + p) + 1)) level [] []⟩) = _
    rw [subtractStep_succ]
    simpa only [List.replicate_succ', List.append_assoc, List.singleton_append] using
      ih (true :: saved) none

/-- Physical unary subtraction preserves the complete count word by moving
its consumed tallies to scratch and then transferring them back. -/
theorem subtractTrace (table query level : List Bool) (k p : Nat) (hkp : k ≤ p)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * k + 2]
      (some ⟨some .subtract, ((ambient, false), register),
        memory table query (encodeWord k) [] [] [] (encodeWord p) level [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory table query (encodeWord k) [] [] [] (encodeWord (p - k)) level [] []⟩ := by
  have hs := subtractScanTrace table query level k (p - k) [] ambient register
  rw [show k + (p - k) = p by omega] at hs
  simp only [List.append_nil] at hs
  let mid := memory table query (encodeWord 0) [] (List.replicate k true) []
    (encodeWord (p - k)) level [] []
  have hr := Reduction.MachineTransfer.transferAt_fromTapes Tape.scratch Tape.count (by decide)
    id false Label.restore none program rfl mid (ambient, false) none
  simp only [mid, memory, List.length_replicate, List.reverse_replicate, List.map_id,
    Reduction.MachineTransfer.tapesAt, update_scratch, update_count] at hr
  rw [MachineCeilingPower.replicate_encodeWord, Nat.add_zero] at hr
  have h := appendTrace_inline_MachineCloudPadding _ hs hr
  simpa only [show (k + 1) + (k + 1) = 2 * k + 2 by omega, Nat.add_zero] using h

theorem branchStep_zero (table query : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some .branch, ((ambient, false), register),
        memory table query (encodeWord 0) [] [] [] [] [] [] []⟩ =
      some ⟨none, ((ambient, false), none),
        memory table query (encodeWord 0) [] [] [] (encodeWord 0) (encodeWord 0) [] []⟩ := by
  simp [TM2.step, program, TM2.stepAux, memory, encodeWord]

theorem branchStep_succ (table query : List Bool) (k : Nat) (ambient : σ)
    (register : Option Bool) :
    TM2.step program
      ⟨some .branch, ((ambient, false), register),
        memory table query (encodeWord (k + 1)) [] [] [] [] [] [] []⟩ =
      some ⟨some (.powerCode .init), ((ambient, false), none),
        memory table query (encodeWord (k + 1)) [] [] [] [] [] [] []⟩ := by
  simp [TM2.step, program, TM2.stepAux, memory, encodeWord, List.replicate_succ]

def padding (k : Nat) : Nat := PreprocessingLevels.cloudPaddedSize k - k

/-- Count zero is handled by a head test. Positive counts execute the exact
power search and subtraction traces on the shared count tape. -/
theorem postTrace (table query : List Bool) (k : Nat) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step program))^[postTime k]
      (some ⟨some .branch, ((ambient, false), register),
        memory table query (encodeWord k) [] [] [] [] [] [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory table query (encodeWord k) [] [] [] (encodeWord (padding k))
          (encodeWord (PreprocessingLevels.boundedLevel k)) [] []⟩ := by
  cases k with
  | zero =>
    simpa only [postTime, ite_eq_left rfl, ite_true, if_true, Nat.add_zero, Function.iterate_one, advance_some,
      padding, PreprocessingLevels.cloudPaddedSize_zero, Nat.sub_zero,
      PreprocessingLevels.boundedLevel_zero] using branchStep_zero table query ambient register
  | succ k =>
    have hb : (advance (TM2.step program))^[1]
        (some ⟨some .branch, ((ambient, false), register),
          memory table query (encodeWord (k + 1)) [] [] [] [] [] [] []⟩) =
        some ⟨some (.powerCode .init), ((ambient, false), none),
          memory table query (encodeWord (k + 1)) [] [] [] [] [] [] []⟩ :=
      branchStep_succ table query k ambient register
    have hp := powerTrace table query (k + 1) ambient none
    have hs := subtractTrace table query (encodeWord (PreprocessingLevels.boundedLevel (k + 1)))
      (k + 1) (PreprocessingLevels.paddedSize (k + 1))
      (PreprocessingLevels.le_paddedSize (k + 1)) ambient none
    have h := appendTrace_inline_MachineCloudPadding _ hb (appendTrace_inline_MachineCloudPadding _ hp hs)
    simpa only [postTime, Nat.succ_ne_zero, ite_false, padding,
      PreprocessingLevels.cloudPaddedSize_of_pos (Nat.succ_pos k)] using h

theorem initStep (table query : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some .init, ((ambient, false), register), memory table query [] [] [] [] [] [] [] []⟩ =
      some ⟨some (.countCode .copyFirst), ((ambient, false), register),
        memory table query (encodeWord 0) [] [] [] [] [] [] []⟩ := by
  simp [TM2.step, program, TM2.stepAux, memory, encodeWord]

/-- One complete concrete program returns the cloud size, geometric level,
and required number of padding vertices, preserving input and query. -/
theorem cloudPaddingTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[totalTime t v]
      (some ⟨some .init, ((ambient, false), register),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix) [] [] [] [] [] [] [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix)
          (encodeWord (PreprocessingCloudIndex.cloudSize t v)) [] [] []
          (encodeWord (padding (PreprocessingCloudIndex.cloudSize t v)))
          (encodeWord (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v)))
          [] []⟩ := by
  have hi : (advance (TM2.step program))^[1]
      (some ⟨some .init, ((ambient, false), register),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix) [] [] [] [] [] [] [] []⟩) =
      some ⟨some (.countCode .copyFirst), ((ambient, false), register),
        memory (GraphTables.tableBits t) (encodeWord v.val ++ suffix)
          (encodeWord 0) [] [] [] [] [] [] []⟩ :=
    initStep _ _ ambient register
  exact appendTrace_inline_MachineCloudPadding _ (appendTrace_inline_MachineCloudPadding _ hi (countTrace t v suffix ambient register))
    (postTrace _ _ (PreprocessingCloudIndex.cloudSize t v) ambient none)

end MaxCutGames.Foundations.Complexity.MachineCloudPadding

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineCloudPrefix
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineCloudPrefix

open Turing MachineComposition
open MaxCutGames.Foundations.PCP
open scoped BigOperators

variable {σ : Type}

def program : Label → TM2.Stmt Alphabet Label (State σ)
  | .init => .push (.inner .query) (fun _ => false)
      (.push .total (fun _ => false) (.goto fun _ => .copyFirst))
  | .copyFirst => Reduction.MachineTransfer.loopAt
      .bound (.inner .scratch) id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop
      (.inner .scratch) .bound .remaining false .copySecond (some .guard)
  | .guard => MachineUnaryCounter.guard .remaining (.padding .init) .done
  | .done => .halt
  | .padding l => MachineCloudPadding.Placement.statement Tape.inner Label.padding (some .add) (MachineCloudPadding.program l)
  | .add => MachineUnaryAddAt.loop (.inner .power) .total .add (some .clearCount)
  | .clearCount => MachineLookup.discard (.inner .count) .clearCount .clearLevel
  | .clearLevel => MachineLookup.discard (.inner .level) .clearLevel .increment
  | .increment => .pop (.inner .power) (fun state _ => (state.1, none))
      (.push (.inner .query) (fun _ => true) (.goto fun _ => .guard))

/-- The inner program is embedded with its actual table scan and geometric
search; all three additional tapes are preserved by every inner transition. -/
theorem paddingTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (bound remaining total : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineCloudPadding.totalTime t v]
      (some ⟨some (.padding .init), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord v.val) [] [] [] bound remaining total⟩) =
      some ⟨some .add, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord v.val)
          (encodeWord (PreprocessingCloudIndex.cloudSize t v))
          (encodeWord (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t v)))
          (encodeWord (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v)))
          bound remaining total⟩ := by
  have h := MachineCloudPadding.Placement.trace Tape.inner paddingView paddingView_left paddingView_right
    Label.padding (some Label.add) (frame [] [] [] [] [] bound remaining total)
    (MachineCloudPadding.program (σ := σ)) program (fun _ => rfl) _ _ _
    (MachineCloudPadding.cloudPaddingTrace t v [] ambient register)
  simpa only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label, placedTapes,
    frame_bound, frame_remaining, frame_total, List.append_nil, frame, memory] using h

theorem incrementStep (table bound remaining total : List Bool) (v : Nat)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .increment, ((ambient, false), register),
        frame table (encodeWord v) [] (encodeWord 0) [] bound remaining total⟩ =
      some ⟨some .guard, ((ambient, false), none),
        frame table (encodeWord (v + 1)) [] [] [] bound remaining total⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord, List.replicate_succ]

def bodyTime (t : GraphTables.Table) (v : Fin t.vertices) : Nat :=
  MachineCloudPadding.totalTime t v + (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t v) + 1) +
    (PreprocessingCloudIndex.cloudSize t v + 1) +
      (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v) + 1) + 1

/-- Padding tallies are consumed by unary addition; count and level fields
are scanned away, and the remaining zero padding delimiter is removed while
the physical vertex counter increases. -/
theorem bodyTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (bound remaining : List Bool) (acc : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[bodyTime t v]
      (some ⟨some (.padding .init), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord v.val) [] [] []
          bound remaining (encodeWord acc)⟩) =
      some ⟨some .guard, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord (v.val + 1)) [] [] []
          bound remaining (encodeWord (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t v) + acc))⟩ := by
  let k := PreprocessingCloudIndex.cloudSize t v
  let p := MachineCloudPadding.padding k
  let l := PreprocessingLevels.boundedLevel k
  have hp := paddingTrace t v bound remaining (encodeWord acc) ambient register
  have ha := MachineUnaryAddAt.addFromTapes (Tape.inner .power) Tape.total (by decide)
    Label.add (some Label.clearCount) program rfl
    (frame (GraphTables.tableBits t) (encodeWord v.val) (encodeWord k)
      (encodeWord p) (encodeWord l) bound remaining (encodeWord acc))
    p acc [] [] (by simp) (by simp) (ambient, false) none
  simp only [MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt,
    List.append_nil, update_frame_power, update_frame_total] at ha
  have hc := MachineLookup.discardTrace (Tape.inner .count) Label.clearCount Label.clearLevel
    program rfl
    (frame (GraphTables.tableBits t) (encodeWord v.val) (encodeWord k)
      (encodeWord 0) (encodeWord l) bound remaining (encodeWord (p + acc)))
    k [] (by simp) (ambient, false) none
  simp only [update_frame_count] at hc
  have hl := MachineLookup.discardTrace (Tape.inner .level) Label.clearLevel Label.increment
    program rfl
    (frame (GraphTables.tableBits t) (encodeWord v.val) []
      (encodeWord 0) (encodeWord l) bound remaining (encodeWord (p + acc)))
    l [] (by simp) (ambient, false) none
  simp only [update_frame_level] at hl
  have hi : (advance (TM2.step program))^[1]
      (some ⟨some .increment, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord v.val) [] (encodeWord 0) []
          bound remaining (encodeWord (p + acc))⟩) =
      some ⟨some .guard, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord (v.val + 1)) [] [] []
          bound remaining (encodeWord (p + acc))⟩ :=
    incrementStep _ _ _ _ _ ambient none
  exact appendTrace_inline_MachineCloudPrefix _ (appendTrace_inline_MachineCloudPrefix _ (appendTrace_inline_MachineCloudPrefix _ (appendTrace_inline_MachineCloudPrefix _ hp ha) hc) hl) hi

theorem guardStep_succ (table bound suffix total : List Bool) (v n : Nat)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .guard, ((ambient, false), register),
        frame table (encodeWord v) [] [] [] bound (encodeWord (n + 1) ++ suffix) total⟩ =
      some ⟨some (.padding .init), ((ambient, false), none),
        frame table (encodeWord v) [] [] [] bound (encodeWord n ++ suffix) total⟩ := by
  simp [TM2.step, program, MachineUnaryCounter.guard, TM2.stepAux, encodeWord,
    List.replicate_succ]

theorem guardStep_zero (table bound suffix total : List Bool) (v : Nat)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .guard, ((ambient, false), register),
        frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩ =
      some ⟨some .done, ((ambient, false), none),
        frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩ := rfl

theorem zeroTrace (table bound suffix total : List Bool) (v : Nat)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[2]
      (some ⟨some .guard, ((ambient, false), register),
        frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩) =
      some ⟨none, ((ambient, false), none),
        frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩ := by
  rw [Function.iterate_succ_apply]
  change advance (TM2.step (program (σ := σ)))
    (TM2.step program ⟨some .guard, ((ambient, false), register),
      frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩) = _
  rw [guardStep_zero]
  rfl

def amount (t : GraphTables.Table) (v : Nat) : Nat :=
  if h : v < t.vertices then MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t ⟨v, h⟩) else 0

def cycleTime (t : GraphTables.Table) (v : Nat) : Nat :=
  if h : v < t.vertices then 1 + bodyTime t ⟨v, h⟩ else 0

def sumFrom (t : GraphTables.Table) (v : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => amount t v + sumFrom t (v + 1) n

def loopTime (t : GraphTables.Table) (v : Nat) : Nat → Nat
  | 0 => 2
  | n + 1 => cycleTime t v + loopTime t (v + 1) n

theorem loopTrace (t : GraphTables.Table) (n v : Nat) (hvn : v + n ≤ t.vertices)
    (bound suffix : List Bool) (acc : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[loopTime t v n]
      (some ⟨some .guard, ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord v) [] [] []
          bound (encodeWord n ++ suffix) (encodeWord acc)⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord (v + n)) [] [] []
          bound (encodeWord 0 ++ suffix) (encodeWord (sumFrom t v n + acc))⟩ := by
  induction n generalizing v acc register with
  | zero =>
      simpa only [loopTime, sumFrom, Nat.add_zero, Nat.zero_add] using
        zeroTrace _ bound suffix (encodeWord acc) v ambient register
  | succ n ih =>
      have hv : v < t.vertices := by omega
      have hnext : v + 1 + n ≤ t.vertices := by omega
      have hg : (advance (TM2.step program))^[1]
          (some ⟨some .guard, ((ambient, false), register),
            frame (GraphTables.tableBits t) (encodeWord v) [] [] []
              bound (encodeWord (n + 1) ++ suffix) (encodeWord acc)⟩) =
          some ⟨some (.padding .init), ((ambient, false), none),
            frame (GraphTables.tableBits t) (encodeWord v) [] [] []
              bound (encodeWord n ++ suffix) (encodeWord acc)⟩ :=
        guardStep_succ _ bound suffix (encodeWord acc) v n ambient register
      have hb := bodyTrace t ⟨v, hv⟩ bound (encodeWord n ++ suffix) acc ambient none
      have ht := ih (v + 1) hnext
        (MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t ⟨v, hv⟩) + acc) none
      have hall := appendTrace_inline_MachineCloudPrefix _ (appendTrace_inline_MachineCloudPrefix _ hg hb) ht
      simpa only [loopTime, cycleTime, dite_eq_left hv, sumFrom, amount,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

theorem sumFrom_list (t : GraphTables.Table) (xs : List (Fin t.vertices)) (v : Nat)
    (hseq : ∀ i (hi : i < xs.length), (xs[i]).val = v + i) :
    sumFrom t v xs.length = (xs.map (PreprocessingRegularTables.padding t)).sum := by
  induction xs generalizing v with
  | nil => simp [sumFrom]
  | cons x xs ih =>
      have hx : x.val = v := by
        have h := hseq 0 (by simp)
        change x.val = v + 0 at h
        simpa only [Nat.add_zero] using h
      have hv : v < t.vertices := by simpa only [hx] using x.isLt
      have he : (⟨v, hv⟩ : Fin t.vertices) = x := Fin.ext hx.symm
      have hnext : ∀ i (hi : i < xs.length), (xs[i]).val = v + 1 + i := by
        intro i hi
        have h := hseq (i + 1) (by simpa using Nat.succ_lt_succ hi)
        simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using h
      simp only [List.length_cons, sumFrom, amount, dite_eq_left hv, he,
        List.map_cons, List.sum_cons]
      rw [ih (v + 1) hnext]
      rfl

theorem sumFrom_eq_offset (t : GraphTables.Table) (b : Nat) (hb : b ≤ t.vertices) :
    sumFrom t 0 b =
      PreprocessingPaddingOffsets.offset (PreprocessingRegularTables.padding t) b := by
  have h := sumFrom_list t ((List.finRange t.vertices).take b) 0
    (by intro i hi; simp only [List.getElem_take, List.getElem_finRange, Fin.val_cast,
      Nat.zero_add])
  simpa only [List.length_take, List.length_finRange, Nat.min_eq_left hb,
    PreprocessingPaddingOffsets.offset] using h

theorem initStep (table bound : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .init, ((ambient, false), register), frame table [] [] [] [] bound [] []⟩ =
      some ⟨some .copyFirst, ((ambient, false), register),
        frame table (encodeWord 0) [] [] [] bound [] (encodeWord 0)⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

def totalTime (t : GraphTables.Table) (b : Nat) (suffix : List Bool) : Nat :=
  (1 + 2 * ((encodeWord b ++ suffix).length + 1)) + loopTime t 0 b

theorem prefixTrace (t : GraphTables.Table) (b : Nat) (hb : b ≤ t.vertices)
    (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[totalTime t b suffix]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] (encodeWord b ++ suffix) [] []⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord b) [] [] []
          (encodeWord b ++ suffix) (encodeWord 0 ++ suffix)
          (encodeWord (PreprocessingPaddingOffsets.offset
            (PreprocessingRegularTables.padding t) b))⟩ := by
  have hi : (advance (TM2.step program))^[1]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] (encodeWord b ++ suffix) [] []⟩) =
      some ⟨some .copyFirst, ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord 0) [] [] []
          (encodeWord b ++ suffix) [] (encodeWord 0)⟩ :=
    initStep _ _ ambient register
  have hc := MachineCopy.copyTrace Tape.bound Tape.remaining (Tape.inner .scratch)
    (by decide) (by decide) (by decide) false Label.copyFirst Label.copySecond
    (some Label.guard) program rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord 0) [] [] []
      (encodeWord b ++ suffix) [] (encodeWord 0)) rfl (ambient, false) register
  simp only [frame_bound, frame_remaining, List.append_nil, update_frame_remaining] at hc
  have hl := loopTrace t b 0 (by simpa only [Nat.zero_add] using hb)
    (encodeWord b ++ suffix) suffix 0 ambient none
  simp only [Nat.zero_add, Nat.add_zero, sumFrom_eq_offset t b hb] at hl
  exact appendTrace_inline_MachineCloudPrefix _ (appendTrace_inline_MachineCloudPrefix _ hi hc) hl

theorem bodyTime_le (t : GraphTables.Table) (v : Fin t.vertices) (L : Nat)
    (hL : (GraphTables.tableBits t).length ≤ L) :
    1 + bodyTime t v ≤ cycleBudget L := by
  have hn := GraphTables.vertices_le_tableBits_length t
  have hv := v.isLt
  have hinput : MachineCloudPadding.inputLength t v [] ≤ 2 * L := by
    simp only [MachineCloudPadding.inputLength, List.append_nil, encodeWord_length]
    omega
  have hp := (MachineCloudPadding.totalTime_le t v []).trans
    (natPolynomial_eval_mono MachineCloudPadding.timePolynomial hinput)
  simp only [MachineCloudPadding.timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] at hp
  have hk : PreprocessingCloudIndex.cloudSize t v ≤ L :=
    (PreprocessingCloudIndex.cloudSize_le_darts t v).trans
      ((GraphTables.darts_le_tableBits_length t).trans hL)
  have hl := (PreprocessingLevels.boundedLevel_le_input
    (PreprocessingCloudIndex.cloudSize t v)).trans hk
  have hpad : MachineCloudPadding.padding (PreprocessingCloudIndex.cloudSize t v) ≤
      ExpanderFamily.growth * L := by
    have hsize := (PreprocessingLevels.cloudPaddedSize_bounds
      (PreprocessingCloudIndex.cloudSize t v)).2
    have hmul := Nat.mul_le_mul_left ExpanderFamily.growth hk
    unfold MachineCloudPadding.padding
    omega
  unfold bodyTime cycleBudget
  simp only [Nat.add_mul] at hp ⊢
  omega

theorem loopTime_le (t : GraphTables.Table) (n v : Nat) (hvn : v + n ≤ t.vertices)
    (L : Nat) (hL : (GraphTables.tableBits t).length ≤ L) :
    loopTime t v n ≤ n * cycleBudget L + 2 := by
  induction n generalizing v with
  | zero => simp only [loopTime, Nat.zero_mul, Nat.zero_add, le_refl]
  | succ n ih =>
      have hv : v < t.vertices := by omega
      have hnext : v + 1 + n ≤ t.vertices := by omega
      have hbody := bodyTime_le t ⟨v, hv⟩ L hL
      have htail := ih (v + 1) hnext
      simp only [loopTime, cycleTime, dite_eq_left hv, Nat.succ_mul]
      omega

/-- The full execution has a cubic polynomial bound in the two actual
preserved input words. The accumulator is never scanned to perform addition. -/
theorem totalTime_le (t : GraphTables.Table) (b : Nat) (hb : b ≤ t.vertices)
    (suffix : List Bool) :
    totalTime t b suffix ≤ timePolynomial.eval (inputLength t b suffix) := by
  let L := inputLength t b suffix
  have htable : (GraphTables.tableBits t).length ≤ L := by
    unfold L inputLength
    omega
  have hbound : (encodeWord b ++ suffix).length ≤ L := by
    unfold L inputLength
    omega
  have hbL : b ≤ L := hb.trans ((GraphTables.vertices_le_tableBits_length t).trans htable)
  have hloop := loopTime_le t b 0 (by simpa only [Nat.zero_add] using hb) L htable
  have hmul := Nat.mul_le_mul_right (cycleBudget L) hbL
  have htotal : totalTime t b suffix ≤ L * cycleBudget L + 2 * (L + 1) + 3 := by
    unfold totalTime
    omega
  simpa only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat,
    Polynomial.eval_one, cycleBudget, L] using htotal

end MaxCutGames.Foundations.Complexity.MachineCloudPrefix

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ExpanderRowControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Raw natural-word serialization of actual expander rotation tables

The list keeps the stored row order `port + degree * vertex`; no header is
inserted. Lookup equalities and complete unary output lengths are data facts,
not machine execution certificates. Kernel-checked with Lean 4.33.1.
-/

namespace MaxCutGames.Foundations.PCP.ExpanderTableWords

open ExpanderTables
open MaxCutGames.Foundations.Complexity (encodeWords decodeWords)

variable {v d : ℕ}

theorem rotationWords_entry_lt (table : Table v d) (n : ℕ)
    (hn : n ∈ rotationWords table) : n < v * d := by
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hn
  exact a.isLt

/-- Complete raw-row serialization bound, with no discarded delimiter or prefix. -/
theorem encode_rotationWords_length_le (table : Table v d) :
    (encodeWords (rotationWords table)).length ≤ (v * d) * (v * d + 1) := by
  calc
    _ ≤ (rotationWords table).length * (v * d + 1) :=
      Complexity.encodeWords_length_le _ _
        (fun n hn => (rotationWords_entry_lt table n hn).le)
    _ = _ := by rw [rotationWords_length]

end MaxCutGames.Foundations.PCP.ExpanderTableWords

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularLift
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineCloudRank

open Turing MachineComposition MachineCloudCount

variable {σ : Type}

def rankProgram : RankLabel → TM2.Stmt Alphabet RankLabel (State σ)
  | .queryFirst => Reduction.MachineTransfer.loopAt
      .target .scratch id false .queryFirst (some .querySecond)
  | .querySecond => MachineCopy.forkLoop
      .scratch .target .spare false .querySecond (some .querySkip)
  | .querySkip => MachineLookup.discard .spare .querySkip .tableFirst
  | .tableFirst => Reduction.MachineTransfer.loopAt
      .original .scratch id false .tableFirst (some .tableSecond)
  | .tableSecond => MachineCopy.forkLoop
      .scratch .original .work false .tableSecond (some .headerFirst)
  | .headerFirst => MachineLookup.discard .work .headerFirst .headerSecond
  | .headerSecond => MachineLookup.discard .work .headerSecond .row
  | .row => MachineUnaryCounter.guard .spare .field .done
  | .field => fieldLoop .field .restore
  | .restore => Reduction.MachineTransfer.loopAt
      .scratch .target id false .restore (some (rankSkip 0))
  | .skip i => MachineLookup.discard .work (.skip i) (rankSkip (i.val + 1))
  | .done => .halt

theorem rankProgram_skip {i : Nat} (hi : i < 4097) :
    rankProgram (σ := σ) (rankSkip i) =
      MachineLookup.discard .work (rankSkip i) (rankSkip (i + 1)) := by
  simp only [rankSkip, dite_eq_left hi, rankProgram]

theorem rowGuard_succ (original work target scratch count fuelSuffix : List Bool)
    (k : Nat) (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (rankProgram (σ := σ))
      ⟨some .row, ((ambient, flag), register),
        memory original work target scratch count (encodeWord (k + 1) ++ fuelSuffix)⟩ =
      some ⟨some .field, ((ambient, flag), none),
        memory original work target scratch count (encodeWord k ++ fuelSuffix)⟩ := by
  change some (TM2.stepAux (rankProgram .row) _ _) = _
  simp [rankProgram, MachineUnaryCounter.guard, TM2.stepAux, encodeWord,
    List.replicate_succ]

theorem rowGuard_zero (original work target scratch count fuelSuffix : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (rankProgram (σ := σ))
      ⟨some .row, ((ambient, flag), register),
        memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩ =
      some ⟨some .done, ((ambient, flag), none),
        memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩ := rfl

theorem zeroRowsTrace (original work target scratch count fuelSuffix : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[2]
      (some ⟨some .row, ((ambient, flag), register),
        memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩) =
      some ⟨none, ((ambient, flag), none),
        memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩ := by
  rw [Function.iterate_succ_apply]
  change advance (TM2.step (rankProgram (σ := σ)))
    (TM2.step rankProgram ⟨some .row, ((ambient, flag), register),
      memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩) = _
  rw [rowGuard_zero]
  rfl

/-- One actual row comparison consumes one unit of fuel and restores the
entire vertex query before discarding the remaining fixed row fields. -/
theorem rankRowTrace (r : Row) (hwidth : r.2.length = 4097) (v k : Nat)
    (original suffix targetSuffix fuelSuffix count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[rowTime v r]
      (some ⟨some .row, ((ambient, false), register),
        memory original (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix)
          [] count (encodeWord (k + 1) ++ fuelSuffix)⟩) =
      some ⟨some .row, ((ambient, false), none),
        memory original suffix (encodeWord v ++ targetSuffix) []
          (List.replicate (if r.1 = v then 1 else 0) true ++ count)
          (encodeWord k ++ fuelSuffix)⟩ := by
  have hfield := preservingFieldTrace RankLabel.field RankLabel.restore (rankSkip 0)
    rankProgram rfl rfl original (encodeWords r.2 ++ suffix) targetSuffix count
    (encodeWord k ++ fuelSuffix) r.1 v ambient none
  have hskip := discardFieldsTrace rankSkip (rankProgram (σ := σ)) r.2 0
    (by intro i hi; simpa only [Nat.zero_add] using rankProgram_skip (hwidth ▸ hi))
    original suffix (encodeWord v ++ targetSuffix) []
    (List.replicate (if r.1 = v then 1 else 0) true ++ count)
    (encodeWord k ++ fuelSuffix) ambient false none
  have hnonempty : r.2 ≠ [] := by intro h; simp [h] at hwidth
  simp only [Nat.zero_add, hwidth, rankSkip, lt_self_iff_false, ↓reduceDIte,
    hnonempty, ite_false] at hskip
  have htime : rowTime v r = (encodeWords r.2).length + (r.1 + min r.1 v + 2) + 1 := by
    simp only [rowTime, rowWords, encodeWords, List.length_append, encodeWord_length]
    omega
  rw [htime, Function.iterate_succ_apply]
  change (advance (TM2.step (rankProgram (σ := σ))))^[
      (encodeWords r.2).length + (r.1 + min r.1 v + 2)]
    (TM2.step rankProgram ⟨some .row, ((ambient, false), register),
      memory original (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix)
        [] count (encodeWord (k + 1) ++ fuelSuffix)⟩) = _
  rw [rowGuard_succ, Function.iterate_add_apply]
  simp only [rowWords, encodeWords, List.append_assoc]
  rw [hfield]
  exact hskip

/-- The row loop runs for the unary fuel on spare, not until the input ends. -/
theorem prefixTrace (rs : List Row) (hwidth : ∀ r ∈ rs, r.2.length = 4097) (v : Nat)
    (original suffix targetSuffix fuelSuffix count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[prefixTime v rs]
      (some ⟨some .row, ((ambient, false), register),
        memory original (encodeWords (rs.flatMap rowWords) ++ suffix)
          (encodeWord v ++ targetSuffix) [] count (encodeWord rs.length ++ fuelSuffix)⟩) =
      some ⟨none, ((ambient, false), none),
        memory original suffix (encodeWord v ++ targetSuffix) []
          (List.replicate (rowsHits v rs) true ++ count) (encodeWord 0 ++ fuelSuffix)⟩ := by
  induction rs generalizing count register with
  | nil =>
      simpa only [prefixTime, List.flatMap_nil, encodeWords, List.nil_append,
        List.length_nil, rowsHits, List.replicate_zero] using
        zeroRowsTrace original suffix (encodeWord v ++ targetSuffix) [] count fuelSuffix
          ambient false register
  | cons r rs ih =>
      have hrow := rankRowTrace r (hwidth r (by simp)) v rs.length original
        (encodeWords (rs.flatMap rowWords) ++ suffix) targetSuffix fuelSuffix count ambient register
      have hrest := ih (by intro x hx; exact hwidth x (by simp [hx]))
        (List.replicate (if r.1 = v then 1 else 0) true ++ count) none
      simp only [prefixTime, List.flatMap_cons, encodeWords_append, List.append_assoc,
        List.length_cons]
      rw [Function.iterate_add_apply, hrow]
      simpa only [rowsHits, ← List.append_assoc, List.replicate_append_replicate,
        Nat.add_comm] using hrest

theorem prefixTime_le (v : Nat) (rs : List Row) :
    prefixTime v rs ≤ 3 * (encodeWords (rs.flatMap rowWords)).length + 2 := by
  induction rs with
  | nil => simp only [prefixTime, List.flatMap_nil, encodeWords, List.length_nil,
      Nat.mul_zero, Nat.zero_add, le_refl]
  | cons r rs ih =>
      have hr := rowTime_le v r
      simp only [prefixTime, List.flatMap_cons, encodeWords_append, List.length_append]
      omega

theorem encoded_rows_split (rs : List Row) (k : Nat) :
    encodeWords (rs.flatMap rowWords) =
      encodeWords ((rs.take k).flatMap rowWords) ++
        encodeWords ((rs.drop k).flatMap rowWords) := by
  have h := congrArg (fun xs : List Row => encodeWords (xs.flatMap rowWords))
    (List.take_append_drop k rs)
  simpa only [List.flatMap_append, encodeWords_append] using h.symm

/-- The full finite trace copies the query, extracts its unary row fuel,
preserves the graph while copying it, skips both headers, and counts a prefix. -/
theorem rankTrace (n m v k : Nat) (rs : List Row) (hk : k ≤ rs.length)
    (hwidth : ∀ r ∈ rs, r.2.length = 4097) (querySuffix count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[rankSteps n m v k rs querySuffix]
      (some ⟨some .queryFirst, ((ambient, false), register),
        memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (inputWord n m rs) (encodeWords ((rs.drop k).flatMap rowWords))
          (queryWord v k querySuffix) []
          (List.replicate (rowsHits v (rs.take k)) true ++ count)
          (encodeWord 0 ++ querySuffix)⟩ := by
  have hquery := MachineCopy.copyTrace Tape.target Tape.spare Tape.scratch
    (by decide) (by decide) (by decide) false RankLabel.queryFirst RankLabel.querySecond
    (some RankLabel.querySkip) rankProgram rfl rfl
    (memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count [])
    rfl (ambient, false) register
  simp only [memory_target, memory_spare, List.append_nil, update_memory_spare] at hquery
  have hquerySkip := MachineLookup.discardTrace Tape.spare RankLabel.querySkip RankLabel.tableFirst
    rankProgram rfl
    (memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count (queryWord v k querySuffix))
    v (encodeWord k ++ querySuffix) rfl (ambient, false) none
  simp only [update_memory_spare] at hquerySkip
  have hcopy := MachineCopy.copyTrace Tape.original Tape.work Tape.scratch
    (by decide) (by decide) (by decide) false RankLabel.tableFirst RankLabel.tableSecond
    (some RankLabel.headerFirst) rankProgram rfl rfl
    (memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count
      (encodeWord k ++ querySuffix)) rfl (ambient, false) none
  simp only [memory_original, memory_work, List.append_nil, update_memory_work] at hcopy
  have hfirst := MachineLookup.discardTrace Tape.work RankLabel.headerFirst RankLabel.headerSecond
    rankProgram rfl
    (memory (inputWord n m rs) (inputWord n m rs) (queryWord v k querySuffix) [] count
      (encodeWord k ++ querySuffix))
    n (encodeWord m ++ encodeWords (rs.flatMap rowWords))
    (inputWord_eq n m rs) (ambient, false) none
  simp only [update_memory_work] at hfirst
  have hsecond := MachineLookup.discardTrace Tape.work RankLabel.headerSecond RankLabel.row
    rankProgram rfl
    (memory (inputWord n m rs) (encodeWord m ++ encodeWords (rs.flatMap rowWords))
      (queryWord v k querySuffix) [] count (encodeWord k ++ querySuffix))
    m (encodeWords (rs.flatMap rowWords)) rfl (ambient, false) none
  simp only [update_memory_work] at hsecond
  have hprefix := prefixTrace (rs.take k)
    (by intro r hr; exact hwidth r (List.mem_of_mem_take hr)) v
    (inputWord n m rs) (encodeWords ((rs.drop k).flatMap rowWords))
    (encodeWord k ++ querySuffix) querySuffix count ambient none
  have htake : (rs.take k).length = k := by
    simp only [List.length_take, Nat.min_eq_left hk]
  rw [htake, ← encoded_rows_split rs k] at hprefix
  rw [show rankSteps n m v k rs querySuffix = prefixTime v (rs.take k) +
      ((m + 1) + ((n + 1) + (2 * ((inputWord n m rs).length + 1) +
        ((v + 1) + 2 * ((queryWord v k querySuffix).length + 1))))) by
      unfold rankSteps; omega,
    Function.iterate_add_apply _ (prefixTime v (rs.take k)),
    Function.iterate_add_apply _ (m + 1), Function.iterate_add_apply _ (n + 1),
    Function.iterate_add_apply _ (2 * ((inputWord n m rs).length + 1)),
    Function.iterate_add_apply _ (v + 1), hquery, hquerySkip, hcopy, hfirst, hsecond]
  exact hprefix

/-- The concrete trace has a linear bound in the two preserved input words. -/
theorem rankSteps_le (n m v k : Nat) (rs : List Row) (querySuffix : List Bool) :
    rankSteps n m v k rs querySuffix ≤
      5 * (inputWord n m rs).length + 3 * (queryWord v k querySuffix).length + 6 := by
  have hprefix := prefixTime_le v (rs.take k)
  have hsplit := congrArg List.length (encoded_rows_split rs k)
  simp only [List.length_append] at hsplit
  have hinput := inputWord_length n m rs
  have hquery : v + 1 ≤ (queryWord v k querySuffix).length := by
    simp only [queryWord, List.length_append, encodeWord_length]
    omega
  unfold rankSteps
  omega

open MaxCutGames.Foundations.PCP

theorem tableRows_length (t : GraphTables.Table) : (tableRows t).length = t.darts := by
  simp only [tableRows, List.length_map, GraphTables.rowList_length]

/-- The executable cloud rank is exactly the count of matching earlier rows. -/
theorem cloudRank_eq_prefix_count (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v) :
    (PreprocessingCloudIndex.cloudRank t v e).val =
      rowsHits v.val ((tableRows t).take e.val.val) := by
  have hindex := idxOf_filter_prefix (fun x : Fin t.darts => decide (t.rows[x].tail = v))
    e.val (by simpa using e.property) (List.finRange t.darts) (List.mem_finRange e.val)
  simp only [List.idxOf_finRange] at hindex
  change (PreprocessingCloudIndex.cloudDarts t v).idxOf e.val = _
  unfold PreprocessingCloudIndex.cloudDarts
  rw [hindex, rowsHits_eq_filter]
  simp only [tableRows, rowList_eq_finRange_map, ← List.map_take, List.filter_map,
    List.length_map, Function.comp_def, Fin.val_inj]

/-- Full trace on a genuine stored graph and a genuine member of its cloud.
The complete input table and the entire vertex/dart query remain unchanged. -/
theorem cloudRankTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v)
    (querySuffix countSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[
        rankSteps t.vertices t.darts v.val e.val.val (tableRows t) querySuffix]
      (some ⟨some .queryFirst, ((ambient, false), register),
        memory (GraphTables.tableBits t) [] (queryWord v.val e.val.val querySuffix) []
          (encodeWord 0 ++ countSuffix) []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (GraphTables.tableBits t)
          (encodeWords (((tableRows t).drop e.val.val).flatMap rowWords))
          (queryWord v.val e.val.val querySuffix) []
          (encodeWord (PreprocessingCloudIndex.cloudRank t v e).val ++ countSuffix)
          (encodeWord 0 ++ querySuffix)⟩ := by
  have hk : e.val.val ≤ (tableRows t).length := by
    rw [tableRows_length]
    exact e.val.isLt.le
  have h := rankTrace t.vertices t.darts v.val e.val.val (tableRows t) hk
    (tableRows_width t) querySuffix (encodeWord 0 ++ countSuffix) ambient register
  rw [tableRows_input, ← cloudRank_eq_prefix_count t v e, ← List.append_assoc,
    replicate_encodeWord, Nat.add_zero] at h
  exact h

end MaxCutGames.Foundations.Complexity.MachineCloudRank

namespace MaxCutGames.Foundations.Complexity.MachineTableRows

open Turing
open PCP.GraphTables

variable {K Λ σ : Type} [DecidableEq K]

/-- The full existing graph codec, including all 4096 unary predicate fields. -/
theorem rowBits_eq {n m : Nat} (r : DartRow n m) :
    encodeWords (rowWords r) = encodeWord r.tail.val ++
      encodeWord r.reverseIndex.val ++ encodeWords (relationWords r.relation) := by
  simp [rowWords, encodeWords]

end MaxCutGames.Foundations.Complexity.MachineTableRows

/-!
# Machine execution for an inherited regularization row

The machine reads the original reverse index from the physically stored input
table. The unread working copy then starts at the 4096 original predicate
fields; a fixed finite Boolean block copy retains exactly those fields. Unary
arithmetic computes the new reverse index, and the checked row emitter appends
the three physical fields. No input table or unbounded arithmetic function is
stored in the machine's finite state or instructions.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineCanonicalOutput
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Canonical output for finite Boolean machines

A raw machine may halt with retained metadata and a changed finite state.
This wrapper redirects its halt to a fixed list of actual tape drains, then
executes one state-reset instruction. The output tape is preserved and the
result is literally `haltList`. Its cost follows from the raw execution and
the maximum number of pushes in a raw statement.

The cleanup list is fixed with the program, not selected from the input.
It may contain repetitions and may be empty when output is the only tape.
-/

namespace MaxCutGames.Foundations.Complexity.MachineCanonicalOutput

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype σ]

def completedProgram (P : Program K Λ σ) (chosen : List K) :
    Label Λ chosen → TM2.Stmt (fun _ : K => Bool) (Label Λ chosen) (σ × Option Bool)
  | .inl label => extendedStmt Sum.inl (cleanupEntry chosen) (P.code label)
  | .inr (.inl label) => MachineDrainMany.instruction chosen (cleanupLabel chosen)
      (some (resetLabel chosen)) label
  | .inr (.inr _) => .load (fun _ => (P.initial, none)) .halt

/-- A fixed finite program over the same Boolean tapes as the raw machine. -/
def completedMachine (P : Program K Λ σ) (chosen : List K) : FinTM2 where
  K := K
  k₀ := P.input
  k₁ := P.output
  Γ _ := Bool
  Λ := Label Λ chosen
  main := .inl P.main
  σ := σ × Option Bool
  initialState := (P.initial, none)
  m := completedProgram P chosen

theorem finiteAlphabet (P : Program K Λ σ) (chosen : List K) :
    MachineFiniteAlphabet.FiniteAlphabet (completedMachine P chosen) := by
  intro k
  exact inferInstanceAs (Finite Bool)

def embeddedCfg (P : Program K Λ σ) (chosen : List K)
    (cfg : (sourceMachine P).Cfg) : (completedMachine P chosen).Cfg :=
  extendedCfg Sum.inl (cleanupEntry chosen) none cfg

theorem step_simulation (P : Program K Λ σ) (chosen : List K)
    (a b : (sourceMachine P).Cfg) (step : (sourceMachine P).step a = some b) :
    (completedMachine P chosen).step (embeddedCfg P chosen a) =
      some (embeddedCfg P chosen b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => simp [FinTM2.step, TM2.step] at step
    | some label =>
      have hb : TM2.stepAux (P.code label) state tapes = b := Option.some.inj step
      rw [← hb]
      change some (TM2.stepAux
        (extendedStmt Sum.inl (cleanupEntry chosen) (P.code label)) (state, none) tapes) = _
      erw [stepAux_extended]
      rfl

@[simp] theorem embedded_init (P : Program K Λ σ) (chosen : List K) (input : List Bool) :
    embeddedCfg P chosen (initList (sourceMachine P) input) =
      initList (completedMachine P chosen) input := rfl

omit [Fintype K] [Fintype Λ] [Fintype σ] in
theorem finalTapes_eq (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output) (base : K → List Bool) :
    MachineDrainMany.finalTapes chosen base =
      MachineDrainMany.haltTapes P.output (base P.output) := by
  funext k
  rw [MachineDrainMany.finalTapes_apply]
  by_cases h : k = P.output
  · subst k
    simp [MachineDrainMany.haltTapes, complete]
  · simp [MachineDrainMany.haltTapes, complete, h]

theorem haltList_eq (P : Program K Λ σ) (chosen : List K) (output : List Bool) :
    haltList (completedMachine P chosen) output =
      ⟨none, (P.initial, none), MachineDrainMany.haltTapes P.output output⟩ := by
  congr 1

noncomputable def completedTime (P : Program K Λ σ) (chosen : List K)
    (rawTime : Polynomial Nat) : Polynomial Nat :=
  rawTime + Polynomial.C chosen.length *
    (Polynomial.X + rawTime * Polynomial.C (Runtime.programPushBound (sourceMachine P)) + 1) + 1

theorem completedTime_eval (P : Program K Λ σ) (chosen : List K)
    (rawTime : Polynomial Nat) (n : Nat) :
    (completedTime P chosen rawTime).eval n =
      rawTime.eval n + chosen.length *
        (n + rawTime.eval n * Runtime.programPushBound (sourceMachine P) + 1) + 1 := by
  simp [completedTime]

/-- An actual raw terminal execution, with arbitrary remaining state and tapes. -/
structure TerminalRun (P : Program K Λ σ) (input output : List Bool) (budget : Nat) where
  state : σ
  tapes : K → List Bool
  execution : StateTransition.EvalsToInTime (sourceMachine P).step
    (initList (sourceMachine P) input) (some ⟨none, state, tapes⟩) budget
  output_eq : tapes P.output = output

end MaxCutGames.Foundations.Complexity.MachineCanonicalOutput

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineCloudSelect
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual inverse cloud numbering. The input table and query are copied
preservingly. A unary working rank decreases only on equal stored tail
fields; a separate unary row position increases on every skipped row.
Only finite phase flags and symbol registers occur in the control state. -/

namespace MaxCutGames.Foundations.Complexity.MachineCloudSelect

open Turing MachineComposition
open MachineCloudCount (Row rowWords rowTime rowsHits tableRows)

variable {σ : Type}

/-- The rest of a row is skipped field by field by the actual fixed program. -/
theorem skipTrace (fields : List Nat) (hwidth : fields.length = 4097)
    (original suffix target rank position : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[(encodeWords fields).length + 1]
      (some (cfg (some (.inl (skipLabel 0))) .advancing original
        (encodeWords fields ++ suffix) target [] rank position ambient none)) =
      some (cfg (some (.inr .dispatch)) .advancing
        original suffix target [] rank position ambient none) := by
  have h := MachineCloudCount.discardFieldsTrace skipLabel (baseProgram (σ := σ)) fields 0
    (by intro i hi; simpa only [Nat.zero_add] using baseProgram_skip (hwidth ▸ hi))
    original suffix target [] [] rank ambient false none
  have hnonempty : fields ≠ [] := by intro h; simp [h] at hwidth
  simp only [Nat.zero_add, hwidth, skipLabel, lt_self_iff_false, ↓reduceDIte,
    hnonempty, ite_false] at h
  have raw : (advance (TM2.step baseProgram))^[(encodeWords fields).length + 1]
      (some ⟨some (skipLabel 0), ((ambient, false), none),
        MachineCloudCount.memory original (encodeWords fields ++ suffix) target [] [] rank⟩) =
      some ⟨none, ((ambient, false), none),
        MachineCloudCount.memory original suffix target [] [] rank⟩ := by
    rw [Function.iterate_succ_apply']
    simp only [skipLabel, dite_eq_left (by decide : 0 < 4097)] at h ⊢
    rw [h, advance_some]
    rfl
  convert liftTrace Phase.advancing position _ _ _ raw using 1 <;> rfl

/-- One nonselected row, with enough remaining rank to pass this row when
it matches. Its global position is incremented on the output tape. -/
theorem rowSkipTrace (r : Row) (hwidth : r.2.length = 4097) (v rank position : Nat)
    (original suffix targetSuffix rankSuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[rowTime v r + 3]
      (some (cfg (some (.inl .field)) .checking original
        (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix) []
        (encodeWord (rank + if r.1 = v then 1 else 0) ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient register)) =
      some (cfg (some (.inl .field)) .checking original suffix
        (encodeWord v ++ targetSuffix) [] (encodeWord rank ++ rankSuffix)
        (encodeWord (position + 1) ++ outputSuffix) ambient none) := by
  have hcompare := compareTrace original (encodeWords r.2 ++ suffix) targetSuffix
    (encodeWord (rank + if r.1 = v then 1 else 0) ++ rankSuffix)
    (encodeWord position ++ outputSuffix) r.1 v ambient register
  have hdispatch : TM2.step program
      (cfg (some (.inr .dispatch)) .checking original (encodeWords r.2 ++ suffix)
        (encodeWord v ++ targetSuffix) (List.replicate (if r.1 = v then 1 else 0) true)
        (encodeWord (rank + if r.1 = v then 1 else 0) ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient none) =
      some (cfg (some (.inl (skipLabel 0))) .advancing original (encodeWords r.2 ++ suffix)
        (encodeWord v ++ targetSuffix) [] (encodeWord rank ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient none) := by
    by_cases hit : r.1 = v
    · simpa only [ite_eq_left hit, List.replicate_succ, List.replicate_zero] using
        dispatch_hit_succ original (encodeWords r.2 ++ suffix) (encodeWord v ++ targetSuffix)
          rankSuffix (encodeWord position ++ outputSuffix) rank ambient
    · simpa only [ite_eq_right hit, Nat.add_zero, List.replicate_zero] using
        dispatch_miss original (encodeWords r.2 ++ suffix) (encodeWord v ++ targetSuffix)
          (encodeWord rank ++ rankSuffix) (encodeWord position ++ outputSuffix) ambient
  have hskip := skipTrace r.2 hwidth original suffix (encodeWord v ++ targetSuffix)
    (encodeWord rank ++ rankSuffix) (encodeWord position ++ outputSuffix) ambient
  have ht : rowTime v r + 3 =
      1 + (((encodeWords r.2).length + 1) + (1 + (r.1 + min r.1 v + 3))) := by
    simp only [rowTime, rowWords, encodeWords, List.length_append, encodeWord_length]
    omega
  rw [ht, Function.iterate_add_apply _ 1,
    Function.iterate_add_apply _ ((encodeWords r.2).length + 1),
    Function.iterate_add_apply _ 1]
  simp only [rowWords, encodeWords, List.append_assoc]
  rw [hcompare, Function.iterate_one, advance_some, hdispatch, hskip,
    advance_some]
  exact advanceStep original suffix (encodeWord v ++ targetSuffix)
    (encodeWord rank ++ rankSuffix) outputSuffix position ambient

/-- A preceding consumes precisely its number of matching tails from unary
rank, while physically counting every original row on the position tape. -/
theorem prefixTrace (rs : List Row) (hwidth : ∀ r ∈ rs, r.2.length = 4097)
    (v rank position : Nat) (original suffix targetSuffix rankSuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[prefixTime v rs]
      (some (cfg (some (.inl .field)) .checking original
        (encodeWords (rs.flatMap rowWords) ++ suffix) (encodeWord v ++ targetSuffix) []
        (encodeWord (rowsHits v rs + rank) ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient register)) =
      some (cfg (some (.inl .field)) .checking original suffix
        (encodeWord v ++ targetSuffix) [] (encodeWord rank ++ rankSuffix)
        (encodeWord (position + rs.length) ++ outputSuffix) ambient
        (if rs = [] then register else none)) := by
  induction rs generalizing position register with
  | nil => simp [prefixTime, rowsHits, encodeWords]
  | cons r rs ih =>
    have hrow := rowSkipTrace r (hwidth r (by simp)) v (rowsHits v rs + rank) position
      original (encodeWords (rs.flatMap rowWords) ++ suffix) targetSuffix rankSuffix
      outputSuffix ambient register
    have hrest := ih (by intro x hx; exact hwidth x (by simp [hx])) (position + 1) none
    simp only [prefixTime, List.flatMap_cons, encodeWords_append, List.append_assoc]
    rw [Function.iterate_add_apply]
    have hi : (if r.1 = v then 1 else 0) + rowsHits v rs + rank =
        (rowsHits v rs + rank) + (if r.1 = v then 1 else 0) := by omega
    simp only [rowsHits, hi]
    rw [hrow]
    simpa only [ite_self, List.cons_ne_nil, ite_false, List.length_cons,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest

/-- Preserve the complete query and table while making the two working
copies; extract the rank and skip the two actual table header fields. -/
theorem prepareTrace (n m v rank : Nat) (rs : List Row)
    (querySuffix position : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[prepareSteps n m v rank rs querySuffix]
      (some (cfg (some (.inl .queryFirst)) .checking (MachineCloudCount.inputWord n m rs)
        [] (queryWord v rank querySuffix) [] [] position ambient register)) =
      some (cfg (some (.inl .field)) .checking (MachineCloudCount.inputWord n m rs)
        (encodeWords (rs.flatMap rowWords)) (queryWord v rank querySuffix) []
        (encodeWord rank ++ querySuffix) position ambient none) := by
  have hquery := MachineCopy.copyTrace MachineCloudCount.Tape.target MachineCloudCount.Tape.spare MachineCloudCount.Tape.scratch
    (by decide) (by decide) (by decide) false BaseLabel.queryFirst BaseLabel.querySecond
    (some BaseLabel.querySkip) baseProgram rfl rfl
    (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs) []
      (queryWord v rank querySuffix) [] [] []) rfl (ambient, false) register
  simp only [MachineCloudCount.memory_target, MachineCloudCount.memory_spare,
    List.append_nil, MachineCloudRank.update_memory_spare] at hquery
  have hquerySkip := MachineLookup.discardTrace MachineCloudCount.Tape.spare BaseLabel.querySkip BaseLabel.tableFirst
    baseProgram rfl (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs) []
      (queryWord v rank querySuffix) [] [] (queryWord v rank querySuffix))
    v (encodeWord rank ++ querySuffix) rfl (ambient, false) none
  simp only [MachineCloudRank.update_memory_spare] at hquerySkip
  have hcopy := MachineCopy.copyTrace MachineCloudCount.Tape.original MachineCloudCount.Tape.work MachineCloudCount.Tape.scratch
    (by decide) (by decide) (by decide) false BaseLabel.tableFirst BaseLabel.tableSecond
    (some BaseLabel.headerFirst) baseProgram rfl rfl
    (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs) []
      (queryWord v rank querySuffix) [] [] (encodeWord rank ++ querySuffix))
    rfl (ambient, false) none
  simp only [MachineCloudCount.memory_original, MachineCloudCount.memory_work,
    List.append_nil, MachineCloudCount.update_memory_work] at hcopy
  have hfirst := MachineLookup.discardTrace MachineCloudCount.Tape.work BaseLabel.headerFirst BaseLabel.headerSecond
    baseProgram rfl (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs)
      (MachineCloudCount.inputWord n m rs) (queryWord v rank querySuffix) [] []
      (encodeWord rank ++ querySuffix))
    n (encodeWord m ++ encodeWords (rs.flatMap rowWords))
    (MachineCloudCount.inputWord_eq n m rs) (ambient, false) none
  simp only [MachineCloudCount.update_memory_work] at hfirst
  have hsecond := MachineLookup.discardTrace MachineCloudCount.Tape.work BaseLabel.headerSecond BaseLabel.field
    baseProgram rfl (MachineCloudCount.memory (MachineCloudCount.inputWord n m rs)
      (encodeWord m ++ encodeWords (rs.flatMap rowWords)) (queryWord v rank querySuffix)
      [] [] (encodeWord rank ++ querySuffix))
    m (encodeWords (rs.flatMap rowWords)) rfl (ambient, false) none
  simp only [MachineCloudCount.update_memory_work] at hsecond
  have raw : (advance (TM2.step baseProgram))^[prepareSteps n m v rank rs querySuffix]
      (some ⟨some .queryFirst, ((ambient, false), register),
        MachineCloudCount.memory (MachineCloudCount.inputWord n m rs) []
          (queryWord v rank querySuffix) [] [] []⟩) =
      some ⟨some .field, ((ambient, false), none),
        MachineCloudCount.memory (MachineCloudCount.inputWord n m rs)
          (encodeWords (rs.flatMap rowWords)) (queryWord v rank querySuffix) [] []
          (encodeWord rank ++ querySuffix)⟩ := by
    rw [show prepareSteps n m v rank rs querySuffix =
        (m + 1) + ((n + 1) + (2 * ((MachineCloudCount.inputWord n m rs).length + 1) +
          ((v + 1) + 2 * ((queryWord v rank querySuffix).length + 1)))) by
          unfold prepareSteps; omega,
      Function.iterate_add_apply _ (m + 1), Function.iterate_add_apply _ (n + 1),
      Function.iterate_add_apply _ (2 * ((MachineCloudCount.inputWord n m rs).length + 1)),
      Function.iterate_add_apply _ (v + 1), hquery, hquerySkip, hcopy, hfirst]
    exact hsecond
  convert liftTrace Phase.checking position _ _ _ raw using 1 <;> rfl

/-- A selected matching field is reached after precisely the matching count
of its actual preceding rows has been consumed from the copied query. -/
theorem prefixSelectedTrace (preceding : List Row)
    (hwidth : ∀ r ∈ preceding, r.2.length = 4097) (v position : Nat)
    (original work targetSuffix rankSuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[prefixTime v preceding + 2 * v + work.length + rankSuffix.length + 8]
      (some (cfg (some (.inl .field)) .checking original
        (encodeWords (preceding.flatMap rowWords) ++ (encodeWord v ++ work))
        (encodeWord v ++ targetSuffix) [] (encodeWord (rowsHits v preceding) ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient register)) =
      some (cfg none .checking original [] (encodeWord v ++ targetSuffix) [] []
        (encodeWord (position + preceding.length) ++ outputSuffix) ambient none) := by
  have hp := prefixTrace preceding hwidth v 0 position original (encodeWord v ++ work)
    targetSuffix rankSuffix outputSuffix ambient register
  simp only [Nat.add_zero] at hp
  have hs := selectedTrace v original work targetSuffix rankSuffix
    (encodeWord (position + preceding.length) ++ outputSuffix) ambient
    (if preceding = [] then register else none)
  rw [show prefixTime v preceding + 2 * v + work.length + rankSuffix.length + 8 =
      (2 * v + work.length + rankSuffix.length + 8) + prefixTime v preceding by omega,
    Function.iterate_add_apply, hp]
  exact hs

/-- Complete execution for the actual encoded preceding decomposition. The
decomposition is semantic data; every machine phase is proved above. -/
theorem fullTrace (n m v rank : Nat) (rs preceding : List Row) (work : List Bool)
    (hwidth : ∀ r ∈ preceding, r.2.length = 4097)
    (hword : encodeWords (rs.flatMap rowWords) =
      encodeWords (preceding.flatMap rowWords) ++ (encodeWord v ++ work))
    (hrank : rank = rowsHits v preceding) (querySuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[totalSteps n m v rank rs preceding work querySuffix]
      (some (cfg (some (.inr .initialize_)) .checking (MachineCloudCount.inputWord n m rs)
        [] (queryWord v rank querySuffix) [] [] outputSuffix ambient register)) =
      some (cfg none .checking (MachineCloudCount.inputWord n m rs) []
        (queryWord v rank querySuffix) [] [] (encodeWord preceding.length ++ outputSuffix) ambient none) := by
  have hp := prepareTrace n m v rank rs querySuffix (encodeWord 0 ++ outputSuffix) ambient none
  have hs := prefixSelectedTrace preceding hwidth v 0 (MachineCloudCount.inputWord n m rs) work
    (encodeWord rank ++ querySuffix) querySuffix outputSuffix ambient none
  simp only [Nat.zero_add] at hs
  rw [← hrank, ← hword] at hs
  rw [show totalSteps n m v rank rs preceding work querySuffix =
      (prefixTime v preceding + 2 * v + work.length + querySuffix.length + 8) +
        (prepareSteps n m v rank rs querySuffix + 1) by unfold totalSteps; omega,
    Function.iterate_add_apply _ (prefixTime v preceding + 2 * v + work.length + querySuffix.length + 8),
    Function.iterate_succ_apply _ (prepareSteps n m v rank rs querySuffix),
    advance_some, initializeStep, hp]
  exact hs

theorem prefixTime_le (v : Nat) (rs : List Row) :
    prefixTime v rs ≤ 6 * (encodeWords (rs.flatMap rowWords)).length := by
  induction rs with
  | nil => simp [prefixTime, encodeWords]
  | cons r rs ih =>
    have hr := MachineCloudCount.rowTime_le v r
    have hpos : 1 ≤ (encodeWords (rowWords r)).length := by
      simp only [rowWords, encodeWords, List.length_append, encodeWord_length]
      omega
    simp only [prefixTime, List.flatMap_cons, encodeWords_append, List.length_append]
    omega

theorem totalSteps_le (n m v rank : Nat) (rs preceding : List Row) (work querySuffix : List Bool)
    (hword : encodeWords (rs.flatMap rowWords) =
      encodeWords (preceding.flatMap rowWords) ++ (encodeWord v ++ work)) :
    totalSteps n m v rank rs preceding work querySuffix ≤
      10 * ((MachineCloudCount.inputWord n m rs).length + (queryWord v rank querySuffix).length) + 20 := by
  have hp := prefixTime_le v preceding
  have hw := congrArg List.length hword
  simp only [List.length_append, encodeWord_length] at hw
  have ht := MachineCloudCount.inputWord_length n m rs
  have hq : (queryWord v rank querySuffix).length =
      v + 1 + (rank + 1) + querySuffix.length := by
    simp only [queryWord, MachineCloudRank.queryWord, List.length_append, encodeWord_length]
    omega
  unfold totalSteps prepareSteps
  omega

open MaxCutGames.Foundations.PCP

/-- Bytes remaining after the selected row's actual tail field. -/
def remainder (t : GraphTables.Table) (e : Fin t.darts) : List Bool :=
  encodeWords (t.rows[e].reverseIndex.val :: GraphTables.relationWords t.rows[e].relation) ++
    encodeWords (((tableRows t).drop (e.val + 1)).flatMap rowWords)

theorem tableRows_getElem (t : GraphTables.Table) (e : Fin t.darts) :
    (tableRows t)[e.val]'(by rw [MachineCloudRank.tableRows_length]; exact e.isLt) =
      (t.rows[e].tail.val, t.rows[e].reverseIndex.val :: GraphTables.relationWords t.rows[e].relation) := by
  simp only [MachineCloudCount.tableRows, MachineCloudCount.rowList_eq_finRange_map,
    List.getElem_map, List.getElem_finRange]
  apply congrArg (fun j : Fin t.darts =>
    (t.rows[j].tail.val, t.rows[j].reverseIndex.val :: GraphTables.relationWords t.rows[j].relation))
  apply Fin.ext
  rfl

/-- Canonical dart indexing yields the literal byte decomposition consumed
by the actual preceding scan and final matching-field test. -/
theorem tableWord_split (t : GraphTables.Table) (v : Fin t.vertices) (e : Fin t.darts)
    (owner : t.rows[e].tail = v) :
    encodeWords ((tableRows t).flatMap rowWords) =
      encodeWords (((tableRows t).take e.val).flatMap rowWords) ++
        (encodeWord v.val ++ remainder t e) := by
  have he : e.val < (tableRows t).length := by
    rw [MachineCloudRank.tableRows_length]
    exact e.isLt
  rw [MachineCloudRank.encoded_rows_split (tableRows t) e.val, List.drop_eq_getElem_cons he]
  simp only [List.flatMap_cons, encodeWords_append]
  rw [tableRows_getElem]
  simp only [rowWords, encodeWords, owner, remainder, List.append_assoc]

def cloudSelectSteps (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v)) (querySuffix : List Bool) : Nat :=
  let e := (PreprocessingCloudIndex.cloudSelect t v i).val
  totalSteps t.vertices t.darts v.val i.val (tableRows t) ((tableRows t).take e.val)
    (remainder t e) querySuffix

theorem cloudSelectTrace (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v)) (querySuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[cloudSelectSteps t v i querySuffix]
      (some (cfg (some (.inr .initialize_)) .checking (GraphTables.tableBits t)
        [] (queryWord v.val i.val querySuffix) [] [] outputSuffix ambient register)) =
      some (cfg none .checking (GraphTables.tableBits t) [] (queryWord v.val i.val querySuffix)
        [] [] (encodeWord (PreprocessingCloudIndex.cloudSelect t v i).val.val ++ outputSuffix)
        ambient none) := by
  let e := PreprocessingCloudIndex.cloudSelect t v i
  have hword := tableWord_split t v e.val e.property
  have hrank : i.val = rowsHits v.val ((tableRows t).take e.val.val) := by
    simpa only [PreprocessingCloudIndex.cloudRank_cloudSelect] using
      MachineCloudRank.cloudRank_eq_prefix_count t v (PreprocessingCloudIndex.cloudSelect t v i)
  have h := fullTrace t.vertices t.darts v.val i.val (tableRows t)
    ((tableRows t).take e.val.val) (remainder t e.val)
    (by intro r hr; exact MachineCloudCount.tableRows_width t r (List.mem_of_mem_take hr))
    hword hrank querySuffix outputSuffix ambient register
  have htake : ((tableRows t).take e.val.val).length = e.val.val := by
    rw [List.length_take, MachineCloudRank.tableRows_length,
      Nat.min_eq_left e.val.isLt.le]
  rw [MachineCloudCount.tableRows_input, htake] at h
  exact h

theorem cloudSelectSteps_le (t : GraphTables.Table) (v : Fin t.vertices)
    (i : Fin (PreprocessingCloudIndex.cloudSize t v)) (querySuffix : List Bool) :
    cloudSelectSteps t v i querySuffix ≤
      10 * ((GraphTables.tableBits t).length + (queryWord v.val i.val querySuffix).length) + 20 := by
  let e := PreprocessingCloudIndex.cloudSelect t v i
  have h := totalSteps_le t.vertices t.darts v.val i.val (tableRows t)
    ((tableRows t).take e.val.val) (remainder t e.val) querySuffix
    (tableWord_split t v e.val e.property)
  simpa only [cloudSelectSteps, e, MachineCloudCount.tableRows_input] using h

end MaxCutGames.Foundations.Complexity.MachineCloudSelect

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineExpanderTableProgram
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} [Fintype ρ]

def rowTapes (vertex : Nat) (oldTable output : List Bool) : MachineExpanderRow.Tape → List Bool
  | .inputVertex => encodeWord vertex
  | .table => oldTable
  | .output => output
  | _ => []

def extraTapes (remaining : Nat) (countSuffix result : List Bool) : ExtraTape → List Bool
  | .vertexCount => encodeWord remaining ++ countSuffix
  | .result => result

def boundaryTapes (vertex remaining : Nat) (oldTable output countSuffix result : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes (rowTapes vertex oldTable output) (extraTapes remaining countSuffix result)

/-- Before initialization, only the old table and remaining-count word are
populated. The program itself creates the initial vertex delimiter. -/
def initialTapes (vertices : Nat) (oldTable countSuffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes
    (fun tape => match tape with | .table => oldTable | _ => [])
    (extraTapes vertices countSuffix [])

def finalTapes (vertices : Nat) (oldTable output countSuffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  boundaryTapes vertices 0 oldTable [] countSuffix output

end MaxCutGames.Foundations.Complexity.MachineExpanderTable

namespace MaxCutGames.Foundations.Complexity.MachineAlphabetTransport

open Turing.TM2

variable {K Λ σ : Type} {Γ Δ : K → Type}

variable [DecidableEq K]

theorem step_simulation (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ) (start : Cfg Γ Λ σ) :
    step (program h source) (configuration h start) =
      (step source start).map (configuration h) := by
  cases h
  simp only [program_rfl, configuration_rfl, map_configuration_rfl]

/-- Exact conjugacy of every finite trace, including a `none` endpoint. -/
theorem trace_transport (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    (n : Nat) (start : Option (Cfg Γ Λ σ)) :
    (MachineComposition.advance (step (program h source)))^[n]
      (start.map (configuration h)) =
      ((MachineComposition.advance (step source))^[n] start).map (configuration h) := by
  cases h
  simp only [program_rfl, map_configuration_rfl]

theorem successfulTrace (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    (n : Nat) (start finish : Cfg Γ Λ σ)
    (trace : (MachineComposition.advance (step source))^[n] (some start) = some finish) :
    (MachineComposition.advance (step (program h source)))^[n]
      (some (configuration h start)) = some (configuration h finish) := by
  have transported := trace_transport h source n (some start)
  simpa only [Option.map_some, trace] using transported

end MaxCutGames.Foundations.Complexity.MachineAlphabetTransport

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

instance alphabetFintype (tape : Tape) : Fintype (Alphabet tape) := by
  rw [alphabet_eq]
  exact inferInstanceAs (Fintype Bool)

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

/-! Static, pointwise Boolean presentation of the actual family tape alphabet.
Every conversion below is an identity on symbols and has no machine runtime. -/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

open Turing

theorem transport_tapes_apply_inline_MachineExpanderFamilyTapes {K : Type} {Γ Δ : K → Type}
    (h : Γ = Δ) (base : (k : K) → List (Γ k)) (k : K) :
    MachineAlphabetTransport.tapes h base k =
      Eq.mp (congrArg (fun alphabet => List (alphabet k)) h) (base k) := by
  cases h
  rfl

theorem toBoolTapes_eq_transport (base : (tape : Tape) → List (Alphabet tape)) :
    toBoolTapes base = MachineAlphabetTransport.tapes alphabet_eq base := by
  funext tape
  rw [transport_tapes_apply_inline_MachineExpanderFamilyTapes]
  rcases tape with tape | tape
  · cases tape <;> rfl
  · rfl

theorem fromBoolTapes_eq_transport (base : Tape → List Bool) :
    fromBoolTapes base = MachineAlphabetTransport.tapes alphabet_eq.symm base := by
  funext tape
  rw [transport_tapes_apply_inline_MachineExpanderFamilyTapes]
  rcases tape with tape | tape
  · cases tape <;> rfl
  · rfl

theorem configuration_fromBool {ρ : Type} {d : Nat} (label : Option (Label d))
    (state : State ρ d) (base : Tape → List Bool) :
    MachineAlphabetTransport.configuration alphabet_eq.symm ⟨label, state, base⟩ =
      ⟨label, state, fromBoolTapes base⟩ := by
  rw [MachineAlphabetTransport.configuration_mk, fromBoolTapes_eq_transport]

theorem configuration_toBool {ρ : Type} {d : Nat} (label : Option (Label d))
    (state : State ρ d) (base : (tape : Tape) → List (Alphabet tape)) :
    MachineAlphabetTransport.configuration alphabet_eq ⟨label, state, base⟩ =
      ⟨label, state, toBoolTapes base⟩ := by
  rw [MachineAlphabetTransport.configuration_mk, toBoolTapes_eq_transport]

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

/-!
# Actual family-table installation and counter cleanup

Checked physical drain and transfer loops are placed in the family program
through its finite register equivalence. Alphabet equality transports their
actual traces back to the dependent alphabet of the full family machine.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

variable [Fintype ρ]

/-- The Boolean view is the same actual program under alphabet equality. -/
theorem boolTraceActual (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (n : Nat)
    (start finish : TM2.Cfg BoolAlphabet (Label d) (State ρ d))
    (run : (advance (TM2.step (boolView positive H growth)))^[n] (some start) = some finish) :
    (advance (TM2.step (program positive H growth)))^[n]
      (some (MachineAlphabetTransport.configuration alphabet_eq.symm start)) =
      some (MachineAlphabetTransport.configuration alphabet_eq.symm finish) := by
  have h := MachineAlphabetTransport.successfulTrace alphabet_eq.symm
    (boolView positive H growth) n start finish run
  simpa only [boolView, MachineAlphabetTransport.program_symm_roundtrip] using h

theorem drainBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (source : Tape) (again next : OuterLabel)
    (code : boolOuterStatement (ρ := ρ) positive H again = drainStatement source again next)
    (base : Tape → List Bool) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[(base source).length + 1]
      (some ⟨some (.inr again), state, base⟩) =
      some ⟨some (.inr next), clearRegister state, Function.update base source []⟩ := by
  have atLoop : boolView (ρ := ρ) positive H growth (.inr again) =
      MachineControl.statement id (registerStates ρ d)
        (MachineDrain.drain source (.inr again) (some (.inr next))) := by
    rw [boolView_outer, code]
    rfl
  have h := controlDrainTrace (registerStates ρ d) source (.inr again) (some (.inr next))
    (boolView positive H growth) atLoop base
    ((registerStates ρ d).symm state).1 ((registerStates ρ d).symm state).2
  simpa only [Prod.mk.eta, Equiv.apply_symm_apply, registerStates_reset] using h

theorem transferBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (source destination : Tape) (distinct : source ≠ destination)
    (again next : OuterLabel)
    (code : boolOuterStatement (ρ := ρ) positive H again =
      MachineControl.statement id (registerStates ρ d)
        (Reduction.MachineTransfer.loopAt (Γ := BoolAlphabet) source destination id false
          (.inr again) (some (.inr next))))
    (base : Tape → List Bool) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[(base source).length + 1]
      (some ⟨some (.inr again), state, base⟩) =
      some ⟨some (.inr next), clearRegister state,
        Reduction.MachineTransfer.tapesAt source destination base []
          ((base source).reverse ++ base destination)⟩ := by
  have atLoop : boolView (ρ := ρ) positive H growth (.inr again) =
      MachineControl.statement id (registerStates ρ d)
        (Reduction.MachineTransfer.loopAt source destination id false
          (.inr again) (some (.inr next))) := by
    rw [boolView_outer, code]
  have h := controlTransferTrace (registerStates ρ d) source destination distinct
    (.inr again) (some (.inr next)) (boolView positive H growth) atLoop base
    ((registerStates ρ d).symm state).1 ((registerStates ρ d).symm state).2
  simpa only [Prod.mk.eta, Equiv.apply_symm_apply, registerStates_reset] using h

/-- Only these four tape words change during installation. -/
def installedTapes (base : Tape → List Bool) (newWord : List Bool) : Tape → List Bool :=
  Function.update
    (Function.update
      (Function.update (Function.update base tableTape newWord) resultTape [])
      (.inr .tableReverse) [])
    (.inr .currentSize) []

def cleanedCounterTapes (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update base inputVertexTape []) vertexCountTape []

theorem installTableBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (newWord : List Bool)
    (resultWord : base resultTape = newWord) (reverseEmpty : base (.inr .tableReverse) = [])
    (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[
        (base tableTape).length + 2 * newWord.length + (base (.inr .currentSize)).length + 4]
      (some ⟨some (.inr .clearOldTable), state, base⟩) =
      some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister state,
        installedTapes base newWord⟩ := by
  let b0 := Function.update base tableTape []
  let b1 := Function.update (Function.update b0 resultTape []) (.inr .tableReverse) newWord.reverse
  let b2 := Function.update (Function.update b1 (.inr .tableReverse) []) tableTape newWord
  let b3 := Function.update b2 (.inr .currentSize) []
  have h0 := drainBoolTrace positive H growth tableTape .clearOldTable .reverseResult rfl base state
  have b0Result : b0 resultTape = newWord := by
    simpa [b0, tableTape, resultTape] using resultWord
  have b0Reverse : b0 (.inr .tableReverse) = [] := by
    simpa [b0, tableTape] using reverseEmpty
  have h1 : (advance (TM2.step (boolView positive H growth)))^[newWord.length + 1]
      (some ⟨some (.inr .reverseResult), clearRegister state, b0⟩) =
      some ⟨some (.inr .reverseTable), clearRegister state, b1⟩ := by
    simpa only [b0Result, b0Reverse, List.append_nil, Reduction.MachineTransfer.tapesAt,
      clearRegister_idempotent] using
      transferBoolTrace positive H growth resultTape (.inr .tableReverse) (by decide)
        .reverseResult .reverseTable rfl b0 (clearRegister state)
  have b1Reverse : b1 (.inr .tableReverse) = newWord.reverse := by simp [b1]
  have b1Table : b1 tableTape = [] := by simp [b1, b0, tableTape, resultTape]
  have h2 : (advance (TM2.step (boolView positive H growth)))^[newWord.length + 1]
      (some ⟨some (.inr .reverseTable), clearRegister state, b1⟩) =
      some ⟨some (.inr .clearCurrentSize), clearRegister state, b2⟩ := by
    simpa only [b1Reverse, b1Table, List.reverse_reverse, List.length_reverse,
      List.append_nil, Reduction.MachineTransfer.tapesAt, clearRegister_idempotent] using
      transferBoolTrace positive H growth (.inr .tableReverse) tableTape (by decide)
        .reverseTable .clearCurrentSize rfl b1 (clearRegister state)
  have b2Current : b2 (.inr .currentSize) = base (.inr .currentSize) := by
    simp [b2, b1, b0, tableTape, resultTape]
  have h3 : (advance (TM2.step (boolView positive H growth)))^[
      (base (.inr .currentSize)).length + 1]
      (some ⟨some (.inr .clearCurrentSize), clearRegister state, b2⟩) =
      some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister state, b3⟩ := by
    simpa only [b2Current, clearRegister_idempotent] using
      drainBoolTrace positive H growth (.inr .currentSize) .clearCurrentSize
        (.affine .multiplySize .seed) rfl b2 (clearRegister state)
  have final : b3 = installedTapes base newWord := by
    funext tape
    rcases tape with table | extra
    · rcases table with row | tableExtra
      · cases row <;> simp [b3, b2, b1, b0, installedTapes, tableTape, resultTape]
      · cases tableExtra <;> simp [b3, b2, b1, b0, installedTapes, tableTape, resultTape]
    · cases extra <;> simp [b3, b2, b1, b0, installedTapes, tableTape, resultTape]
  rw [show (base tableTape).length + 2 * newWord.length +
        (base (.inr .currentSize)).length + 4 =
      ((base (.inr .currentSize)).length + 1) +
        ((newWord.length + 1) + ((newWord.length + 1) + ((base tableTape).length + 1))) by omega,
    Function.iterate_add_apply _ ((base (.inr .currentSize)).length + 1),
    Function.iterate_add_apply _ (newWord.length + 1) ((newWord.length + 1) + ((base tableTape).length + 1)),
    Function.iterate_add_apply _ (newWord.length + 1) ((base tableTape).length + 1),
    h0, h1, h2, h3, final]

theorem cleanupCountersBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[
        (base inputVertexTape).length + (base vertexCountTape).length + 2]
      (some ⟨some (.inr .drainInputVertex), state, base⟩) =
      some ⟨some (.inr .levelGuard), clearRegister state, cleanedCounterTapes base⟩ := by
  have h0 := drainBoolTrace positive H growth inputVertexTape .drainInputVertex .drainVertexCount
    rfl base state
  have count : (Function.update base inputVertexTape []) vertexCountTape = base vertexCountTape := by
    simp [inputVertexTape, vertexCountTape]
  have h1 := drainBoolTrace positive H growth vertexCountTape .drainVertexCount .levelGuard
    rfl (Function.update base inputVertexTape []) (clearRegister state)
  simp only [count, clearRegister_idempotent] at h1
  rw [show (base inputVertexTape).length + (base vertexCountTape).length + 2 =
      ((base vertexCountTape).length + 1) + ((base inputVertexTape).length + 1) by omega,
    Function.iterate_add_apply, h0]
  exact h1

/-- Actual dependent-alphabet trace for draining the old table, installing the
new forward table by two physical reversals, and clearing the old size word. -/
theorem installTableTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (newWord : List Bool) (resultWord : toBoolTapes base resultTape = newWord)
    (reverseEmpty : toBoolTapes base (.inr .tableReverse) = []) (state : State ρ d) :
    (advance (TM2.step (program positive H growth)))^[
        (toBoolTapes base tableTape).length + 2 * newWord.length +
          (toBoolTapes base (.inr .currentSize)).length + 4]
      (some ⟨some (.inr .clearOldTable), state, base⟩) =
      some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister state,
        fromBoolTapes (installedTapes (toBoolTapes base) newWord)⟩ := by
  have h := installTableBoolTrace positive H growth (toBoolTapes base) newWord resultWord reverseEmpty state
  simpa only [configuration_fromBool, fromBool_toBool] using boolTraceActual positive H growth _ _ _ h

/-- After the checked affine phase, both table-loop counters are physically
drained and the actual family level guard is reached. -/
theorem cleanupCountersTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (state : State ρ d) :
    (advance (TM2.step (program positive H growth)))^[
        (toBoolTapes base inputVertexTape).length + (toBoolTapes base vertexCountTape).length + 2]
      (some ⟨some (.inr .drainInputVertex), state, base⟩) =
      some ⟨some (.inr .levelGuard), clearRegister state,
        fromBoolTapes (cleanedCounterTapes (toBoolTapes base))⟩ := by
  have h := cleanupCountersBoolTrace positive H growth (toBoolTapes base) state
  simpa only [configuration_fromBool, fromBool_toBool] using boolTraceActual positive H growth _ _ _ h

def installTableInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (newWord : List Bool) (resultWord : toBoolTapes base resultTape = newWord)
    (reverseEmpty : toBoolTapes base (.inr .tableReverse) = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .clearOldTable), state, base⟩
      (some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister state,
        fromBoolTapes (installedTapes (toBoolTapes base) newWord)⟩)
      ((toBoolTapes base tableTape).length + 2 * newWord.length +
        (toBoolTapes base (.inr .currentSize)).length + 4) where
  steps := (toBoolTapes base tableTape).length + 2 * newWord.length +
    (toBoolTapes base (.inr .currentSize)).length + 4
  evals_in_steps := installTableTrace positive H growth base newWord resultWord reverseEmpty state
  steps_le_m := Nat.le_refl _

def cleanupCountersInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .drainInputVertex), state, base⟩
      (some ⟨some (.inr .levelGuard), clearRegister state,
        fromBoolTapes (cleanedCounterTapes (toBoolTapes base))⟩)
      ((toBoolTapes base inputVertexTape).length + (toBoolTapes base vertexCountTape).length + 2) where
  steps := (toBoolTapes base inputVertexTape).length + (toBoolTapes base vertexCountTape).length + 2
  evals_in_steps := cleanupCountersTrace positive H growth base state
  steps_le_m := Nat.le_refl _

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineExpanderFamilyAffine
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

theorem affine_source_ne_scratch (phase : AffinePhase) :
    affineSource phase ≠ .inr .unaryScratch := by cases phase <;> decide

theorem affine_source_ne_destination (phase : AffinePhase) :
    affineSource phase ≠ affineDestination phase := by cases phase <;> decide

theorem affine_scratch_ne_destination (phase : AffinePhase) :
    (.inr .unaryScratch : Tape) ≠ affineDestination phase := by cases phase <;> decide

/-- Exact final dependent tape family, with all other tape contents retained. -/
def affineResultTapes (d : Nat) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) :
    (tape : Tape) → List (Alphabet tape) :=
  Function.update base (affineDestination phase)
    (boolWord (affineDestination phase)
      (encodeWord (affineCoefficient d phase * n) ++ toBoolTapes base (affineDestination phase)))

variable {ρ : Type} [Fintype ρ] {d : Nat}

/-- The concrete Boolean view is pulled into unary-affine state coordinates,
executed from its actual statements, and transported back without extra steps. -/
theorem affinePhaseBoolTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (phase : AffinePhase) (base : Tape → List Bool)
    (n : Nat) (suffix : List Bool)
    (sourceWord : base (affineSource phase) = encodeWord n ++ suffix)
    (scratchEmpty : base (.inr .unaryScratch) = []) (state : State ρ d) :
    (advance (TM2.step (boolView positive H growth)))^[2 * (n + 1) + 1]
      (some ⟨some (.inr (.affine phase .seed)), state, base⟩) =
      some ⟨some (affineExit d phase), clearRegister state,
        Function.update base (affineDestination phase)
          (encodeWord (affineCoefficient d phase * n) ++ base (affineDestination phase))⟩ := by
  let states := registerStates ρ d
  let target := boolView (ρ := ρ) positive H growth
  let sourceProgram := MachineControl.program (Equiv.refl (Label d)) states.symm target
  have atSeed : sourceProgram (.inr (.affine phase .seed)) =
      MachineUnaryAffineAt.seed (affineDestination phase) 0 (.inr (.affine phase .scan)) := by
    change MachineControl.statement id states.symm
      (boolView positive H growth (.inr (.affine phase .seed))) = _
    rw [boolView_outer]
    exact controlStatementInverse states _
  have atScan : sourceProgram (.inr (.affine phase .scan)) =
      MachineUnaryAffineAt.scan (affineSource phase) (.inr .unaryScratch)
        (affineDestination phase) (affineCoefficient d phase)
        (.inr (.affine phase .scan)) (.inr (.affine phase .restore)) := by
    change MachineControl.statement id states.symm
      (boolView positive H growth (.inr (.affine phase .scan))) = _
    rw [boolView_outer]
    exact controlStatementInverse states _
  have atRestore : sourceProgram (.inr (.affine phase .restore)) =
      Reduction.MachineTransfer.loopAt (.inr .unaryScratch) (affineSource phase) id false
        (.inr (.affine phase .restore)) (some (affineExit d phase)) := by
    change MachineControl.statement id states.symm
      (boolView positive H growth (.inr (.affine phase .restore))) = _
    rw [boolView_outer]
    exact controlStatementInverse states _
  have raw := MachineUnaryAffineAt.seededAffineTrace
    (affineSource phase) (.inr .unaryScratch) (affineDestination phase)
    (affine_source_ne_scratch phase) (affine_source_ne_destination phase)
    (affine_scratch_ne_destination phase) (affineCoefficient d phase) 0
    (.inr (.affine phase .seed)) (.inr (.affine phase .scan)) (.inr (.affine phase .restore))
    (some (affineExit d phase)) sourceProgram atSeed atScan atRestore base n suffix
    sourceWord scratchEmpty (states.symm state).1 (states.symm state).2
  have run := controlTrace states target (2 * (n + 1) + 1) _ _ raw
  simpa only [states, target, MachineControl.configuration, Option.map_some, id_eq, Prod.mk.eta,
    Equiv.apply_symm_apply, Nat.add_zero, registerStates_reset] using run

/-- Actual family-program execution. Alphabet conversion is static equality
transport; the transition count is exactly the checked unary-affine count. -/
theorem affinePhaseTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) (suffix : List Bool)
    (sourceWord : toBoolTapes base (affineSource phase) = encodeWord n ++ suffix)
    (scratchEmpty : base (.inr .unaryScratch) = []) (state : State ρ d) :
    (advance (TM2.step (program positive H growth)))^[2 * (n + 1) + 1]
      (some ⟨some (.inr (.affine phase .seed)), state, base⟩) =
      some ⟨some (affineExit d phase), clearRegister state,
        affineResultTapes d phase base n⟩ := by
  have raw := affinePhaseBoolTrace positive H growth phase (toBoolTapes base) n suffix
    sourceWord scratchEmpty state
  have transported := boolTraceActual positive H growth (2 * (n + 1) + 1) _ _ raw
  simpa only [configuration_fromBool, fromBoolTapes_update, fromBool_toBool,
    affineResultTapes] using transported

def affinePhaseInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (phase : AffinePhase)
    (base : (tape : Tape) → List (Alphabet tape)) (n : Nat) (suffix : List Bool)
    (sourceWord : toBoolTapes base (affineSource phase) = encodeWord n ++ suffix)
    (scratchEmpty : base (.inr .unaryScratch) = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr (.affine phase .seed)), state, base⟩
      (some ⟨some (affineExit d phase), clearRegister state,
        affineResultTapes d phase base n⟩) (2 * (n + 1) + 1) where
  steps := 2 * (n + 1) + 1
  evals_in_steps := affinePhaseTrace positive H growth phase base n suffix sourceWord scratchEmpty state
  steps_le_m := Nat.le_refl _

def copyCountInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (n : Nat) (sourceWord : base (.inr .currentSize) = encodeWord n)
    (scratchEmpty : base (.inr .unaryScratch) = [])
    (destinationEmpty : base vertexCountTape = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr (.affine .copyCount .seed)), state, base⟩
      (some ⟨some (.inl (.inr .initialize_)), clearRegister state,
        Function.update base vertexCountTape (encodeWord n)⟩) (2 * (n + 1) + 1) := by
  have run := affinePhaseInTime positive H growth .copyCount base n []
    (by simpa only [affineSource, toBoolTapes, toBoolWord, List.append_nil] using sourceWord)
    scratchEmpty state
  change base (.inl (.inr .vertexCount)) = [] at destinationEmpty
  simpa only [affineExit, affineResultTapes, affineDestination, affineCoefficient,
    Nat.one_mul, vertexCountTape, boolWord, toBoolTapes, toBoolWord,
    destinationEmpty, List.append_nil] using run

def multiplySizeInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : (tape : Tape) → List (Alphabet tape))
    (n : Nat) (sourceWord : base inputVertexTape = encodeWord n)
    (scratchEmpty : base (.inr .unaryScratch) = [])
    (destinationEmpty : base (.inr .currentSize) = []) (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr (.affine .multiplySize .seed)), state, base⟩
      (some ⟨some (.inr .drainInputVertex), clearRegister state,
        Function.update base (.inr .currentSize) (encodeWord (cloudSize d * n))⟩)
      (2 * (n + 1) + 1) := by
  have run := affinePhaseInTime positive H growth .multiplySize base n []
    (by simpa only [affineSource, inputVertexTape, toBoolTapes, toBoolWord,
      List.append_nil] using sourceWord)
    scratchEmpty state
  simpa only [affineExit, affineResultTapes, affineDestination, affineCoefficient,
    boolWord, toBoolTapes, toBoolWord, destinationEmpty, List.append_nil] using run

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

/-!
# Actual lookup and reversal phases of the expander row program

The Boolean phase selector chooses the first or second occurrence of the same
preserving lookup. The selected word is proved to be the actual stored reverse
index of the supplied graph row. All execution facts follow from the concrete
program statements; no phase execution is assumed.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineExpanderRowFrames
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete data and tape frames for an actual expander-row computation

Only the five actual row inputs are stored. Every address, table return and
finite control value below is computed from those inputs. The thirteen tape
frames use the existing phase-output functions. These are data identities and
size bounds, not assumed machine executions.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderRow

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

namespace RowData

variable {v d : Nat} (r : RowData v d)

def tableLength : Nat := (encodeWords (rotationWords r.oldTable)).length

end RowData

/-! Direct input facts for the individual checked phase traces. -/

end MaxCutGames.Foundations.Complexity.MachineExpanderRow

/-!
# Complete execution of one expander-table row

The actual finite program performs both stored-table lookups, splits their
results by its fixed degree, emits the resulting square/zigzag reverse index,
and clears its work tapes. Its transition bound is linear in the unary input
table length. The output accumulator and finite caller state are arbitrary.
-/

/-!
# Concrete boundary steps of the expander-table machine

Every execution theorem below reduces the actual common program statement.
States and dependent tape frames are arbitrary; only the relevant unary word
or finite-position branch is specified. No phase execution is a premise.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

theorem nextPosition_val_of_lt (positive : 0 < d) (position : Position d)
    (more : position.val + 1 < rowFactor d) :
    (nextPosition positive position).val = position.val + 1 := Nat.mod_eq_of_lt more

/-- Replacing the count word leaves the entire row frame and result unchanged. -/
theorem boundaryTapes_update_count (vertex remaining next : Nat)
    (oldTable output countSuffix result : List Bool) :
    Function.update (boundaryTapes vertex remaining oldTable output countSuffix result)
      (.inr .vertexCount) (encodeWord next ++ countSuffix) =
      boundaryTapes vertex next oldTable output countSuffix result := by
  funext tape
  rcases tape with row | extra
  · cases row <;> simp [boundaryTapes, rowTapes, MachineEmbedding.tapes, Function.update]
  · cases extra <;> simp [boundaryTapes, extraTapes, MachineEmbedding.tapes, Function.update]

/-- The last row's one actual push increments the unary vertex word. -/
theorem boundaryTapes_increment_vertex (vertex remaining : Nat)
    (oldTable output countSuffix result : List Bool) :
    Function.update (boundaryTapes vertex remaining oldTable output countSuffix result)
      (.inl .inputVertex) (true :: encodeWord vertex) =
      boundaryTapes (vertex + 1) remaining oldTable output countSuffix result := by
  funext tape
  rcases tape with row | extra
  · cases row <;>
      simp [boundaryTapes, rowTapes, MachineEmbedding.tapes, Function.update,
        encodeWord, List.replicate_succ]
  · cases extra <;>
      simp [boundaryTapes, extraTapes, MachineEmbedding.tapes, Function.update]

variable [Fintype ρ]

/-- A positive vertex counter is physically decremented; its suffix remains. -/
theorem vertexGuard_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (remaining : Nat) (suffix : List Bool)
    (counter : base (.inr .vertexCount) = encodeWord (remaining + 1) ++ suffix) :
    TM2.step (program positive H) ⟨some (.inr .vertexGuard), state, base⟩ =
      some ⟨some (.inr .prepareRow), clearRegister state,
        Function.update base (.inr .vertexCount) (encodeWord remaining ++ suffix)⟩ := by
  change some (TM2.stepAux (program positive H (.inr .vertexGuard)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, vertexGuardCore, TM2.stepAux,
    guardStates, clearRegister, counter, encodeWord, List.replicate_succ]

/-- The zero delimiter is retained when the loop enters output reversal. -/
theorem vertexGuard_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (suffix : List Bool)
    (counter : base (.inr .vertexCount) = encodeWord 0 ++ suffix) :
    TM2.step (program positive H) ⟨some (.inr .vertexGuard), state, base⟩ =
      some ⟨some (.inr .reverseOutput), clearRegister state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .vertexGuard)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, vertexGuardCore, TM2.stepAux,
    guardStates, clearRegister, counter, encodeWord]

theorem vertexGuard_boundary_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    TM2.step (program positive H)
      ⟨some (.inr .vertexGuard), state,
        boundaryTapes vertex (remaining + 1) oldTable output countSuffix result⟩ =
      some ⟨some (.inr .prepareRow), clearRegister state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩ := by
  simpa only [boundaryTapes_update_count] using
    vertexGuard_succStep positive H
      (boundaryTapes vertex (remaining + 1) oldTable output countSuffix result)
      state remaining countSuffix rfl

theorem vertexGuard_boundary_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex : Nat) (oldTable output countSuffix result : List Bool) (state : State ρ d) :
    TM2.step (program positive H)
      ⟨some (.inr .vertexGuard), state,
        boundaryTapes vertex 0 oldTable output countSuffix result⟩ =
      some ⟨some (.inr .reverseOutput), clearRegister state,
        boundaryTapes vertex 0 oldTable output countSuffix result⟩ :=
  vertexGuard_zeroStep positive H
    (boundaryTapes vertex 0 oldTable output countSuffix result) state countSuffix rfl

/-- A nonfinal row advances the finite position without changing tapes. -/
theorem afterRow_moreStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (more : state.2.val + 1 < rowFactor d) :
    TM2.step (program positive H) ⟨some (.inr .afterRow), state, base⟩ =
      some ⟨some (.inr .prepareRow), advancePositionState positive state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .afterRow)) state base) = _
  rw [program_outer]
  simp [outerStatement, TM2.stepAux, more]

/-- The final row increments the tape vertex and resets the finite position. -/
theorem afterRow_lastStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (last : ¬ state.2.val + 1 < rowFactor d) :
    TM2.step (program positive H) ⟨some (.inr .afterRow), state, base⟩ =
      some ⟨some (.inr .vertexGuard), resetPositionState positive state,
        Function.update base (.inl .inputVertex) (true :: base (.inl .inputVertex))⟩ := by
  change some (TM2.stepAux (program positive H (.inr .afterRow)) state base) = _
  rw [program_outer]
  simp [outerStatement, TM2.stepAux, last]

/-- One reversal step moves an actual symbol and preserves the finite position. -/
theorem reverseOutput_consStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (symbol : Bool) (word : List Bool) (source : base (.inl .output) = symbol :: word) :
    TM2.step (program positive H) ⟨some (.inr .reverseOutput), state, base⟩ =
      some ⟨some (.inr .reverseOutput), ((state.1.1, some symbol), state.2),
        Function.update (Function.update base (.inl .output) word)
          (.inr .result) (symbol :: base (.inr .result))⟩ := by
  change some (TM2.stepAux (program positive H (.inr .reverseOutput)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, Reduction.MachineTransfer.loopAt,
    Reduction.MachineTransfer.exitAt, TM2.stepAux, guardStates, source]

theorem reverseOutput_nilStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (source : base (.inl .output) = []) :
    TM2.step (program positive H) ⟨some (.inr .reverseOutput), state, base⟩ =
      some ⟨some (.inr .done), clearRegister state, base⟩ := by
  have same : Function.update base (.inl .output) [] = base := by
    simpa only [source] using Function.update_eq_self (.inl .output) base
  change some (TM2.stepAux (program positive H (.inr .reverseOutput)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, Reduction.MachineTransfer.loopAt,
    Reduction.MachineTransfer.exitAt, TM2.stepAux, guardStates, clearRegister, source, same]

theorem doneStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H) ⟨some (.inr .done), state, base⟩ =
      some ⟨none, state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .done)) state base) = _
  rw [program_outer]
  rfl

end MaxCutGames.Foundations.Complexity.MachineExpanderTable

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ExpanderTableEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact row enumeration and accumulator contents for an expander-table step

The outer loop enumerates original vertices, and the inner loop enumerates
cloud/port positions in increasing mixed-radix order. The resulting list is
the actual next table's stored rotation-word list. Prefix and reverse-encoding
identities describe data accumulated by a row loop; they assert no runtime.
-/

namespace MaxCutGames.Foundations.PCP.ExpanderTableEnumeration

open ExpanderTables ExpanderRowControl ExpanderTableWords
open MaxCutGames.Foundations.Complexity

variable {v d : Nat}

theorem priorVertices_succ (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (k : Nat) (hk : k < v) :
    priorVertices G H (k + 1) = priorVertices G H k ++ vertexWords G H ⟨k, hk⟩ := by
  unfold priorVertices
  rw [List.take_succ_eq_append_getElem (by simpa using hk), List.flatten_append]
  simp

theorem accumulate_eq (values : List Nat) (initial : List Bool) :
    accumulate values initial = (encodeWords values).reverse ++ initial := by
  induction values generalizing initial with
  | nil => simp [accumulate, encodeWords]
  | cons value values ih =>
      simpa only [accumulate, List.foldl_cons, encodeWords, List.reverse_append,
        List.append_assoc] using ih ((encodeWord value).reverse ++ initial)

theorem accumulate_append (first second : List Nat) (initial : List Bool) :
    accumulate (first ++ second) initial = accumulate second (accumulate first initial) := by
  simp only [accumulate, List.foldl_append]

theorem accumulate_generatedWords (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (initial : List Bool) :
    accumulate (generatedWords G H) initial =
      (encodeWords (rotationWords (step G H))).reverse ++ initial := by
  rw [accumulate_eq, generatedWords_eq_rotationWords]

theorem encode_generatedWords_length_le (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    (encodeWords (generatedWords G H)).length ≤
      (v * rowFactor d) * (v * rowFactor d + 1) := by
  rw [generatedWords_eq_rotationWords, rowCount_eq]
  exact encode_rotationWords_length_le (step G H)

end MaxCutGames.Foundations.PCP.ExpanderTableEnumeration

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineExpanderTableRows
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual execution of all expander-table positions for one vertex

The inner loop calls the complete row machine once per fixed cloud/port position.
The returned state and the successful machine execution are constructed together.
Neither a row execution nor an inner-loop execution is a caller premise.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

variable {ρ : Type} [Fintype ρ] {v d : Nat}

/-- A successful suffix of the finite position loop, returning actual finite
state together with the execution certificate and its preserved caller. -/
structure VertexSuffixRun (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (remaining : Nat) (output countSuffix result : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  position_zero : finalState.2 = zeroPosition positive
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H))
    ⟨some (.inr .prepareRow), state,
      boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result⟩
    (some ⟨some (.inr .vertexGuard), finalState,
      boundaryTapes (vertex.val + 1) remaining (encodeWords (rotationWords G))
        (accumulate ((vertexWords G H vertex).drop state.2.val) output) countSuffix result⟩)
    ((rowFactor d - state.2.val) * (80 * ((encodeWords (rotationWords G)).length + 1) + 2))

/-- The complete inner loop for one vertex, starting at position zero. -/
structure VertexRun (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (remaining : Nat) (output countSuffix result : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  position_zero : finalState.2 = zeroPosition positive
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H))
    ⟨some (.inr .prepareRow), state,
      boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result⟩
    (some ⟨some (.inr .vertexGuard), finalState,
      boundaryTapes (vertex.val + 1) remaining (encodeWords (rotationWords G))
        (accumulate (vertexWords G H vertex) output) countSuffix result⟩)
    (rowFactor d * (80 * ((encodeWords (rotationWords G)).length + 1) + 2))

end MaxCutGames.Foundations.Complexity.MachineExpanderTable

/-!
# Actual outer vertex iteration for expander tables

The invariant is the reversed unary encoding of all completed vertices. Each
positive unary guard invokes the proved complete fixed-position row loop;
the zero guard enters the actual output-reversal phase. No execution premise
is supplied by the caller.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderTable

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

theorem accumulatedVertices_succ {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (current : Nat) (valid : current < v) :
    accumulatedVertices G H (current + 1) =
      accumulate (vertexWords G H ⟨current, valid⟩) (accumulatedVertices G H current) := by
  simp only [accumulatedVertices, priorVertices_succ G H current valid, accumulate_append]

theorem accumulatedVertices_full {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) : accumulatedVertices G H v =
      (encodeWords (rotationWords (step G H))).reverse := by
  simp [accumulatedVertices, accumulate_generatedWords]

def vertexBodyBudget {v d : Nat} (G : Table v (degree d)) : Nat :=
  rowFactor d * (80 * ((oldTableWord G).length + 1) + 2)

def vertexLoopBudget {v d : Nat} (G : Table v (degree d)) (remaining : Nat) : Nat :=
  remaining * (vertexBodyBudget G + 1) + 1

def vertexLoopTapes {v d : Nat} (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (current remaining : Nat) (suffix : List Bool) : ∀ tape, List (Alphabet tape) :=
  boundaryTapes current remaining (oldTableWord G) (accumulatedVertices G H current) suffix []

structure VertexLoopRun {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (current remaining : Nat) (state : State ρ d) (suffix : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  position_zero : finalState.2 = zeroPosition positive
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H))
    ⟨some (.inr .vertexGuard), state, vertexLoopTapes G H current remaining suffix⟩
    (some ⟨some (.inr .reverseOutput), finalState, vertexLoopTapes G H v 0 suffix⟩)
    (vertexLoopBudget G remaining)

end MaxCutGames.Foundations.Complexity.MachineExpanderTable

namespace MaxCutGames.Foundations.Complexity.MachineExpanderTable

open Turing
open MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

theorem boundaryTapes_reverse_update (vertex remaining : Nat)
    (oldTable output countSuffix result nextOutput nextResult : List Bool) :
    Function.update
      (Function.update (boundaryTapes vertex remaining oldTable output countSuffix result)
        (.inl .output) nextOutput)
      (.inr .result) nextResult =
      boundaryTapes vertex remaining oldTable nextOutput countSuffix nextResult := by
  funext tape
  rcases tape with row | extra
  · cases row <;>
      simp [boundaryTapes, rowTapes, MachineEmbedding.tapes, Function.update]
  · cases extra <;>
      simp [boundaryTapes, extraTapes, MachineEmbedding.tapes, Function.update]

variable [Fintype ρ]

/-- Exact execution of the entire final reverse loop, including its empty
test. No reversal-execution hypothesis is assumed. -/
theorem reverseOutputTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    (advance (TM2.step (program positive H)))^[output.length + 1]
      (some ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩) =
      some ⟨some (.inr .done), clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩ := by
  induction output generalizing result state with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, advance_some,
        List.reverse_nil, List.nil_append] using
        reverseOutput_nilStep positive H
          (boundaryTapes vertex remaining oldTable [] countSuffix result) state rfl
  | cons symbol output ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [reverseOutput_consStep positive H
        (boundaryTapes vertex remaining oldTable (symbol :: output) countSuffix result)
        state symbol output rfl]
      change (advance (TM2.step (program positive H)))^[output.length + 1]
        (some ⟨some (.inr .reverseOutput), ((state.1.1, some symbol), state.2),
          Function.update
            (Function.update
              (boundaryTapes vertex remaining oldTable (symbol :: output) countSuffix result)
              (.inl .output) output)
            (.inr .result) (symbol :: result)⟩) = _
      rw [boundaryTapes_reverse_update]
      simpa only [clearRegister, List.reverse_cons, List.append_assoc,
        List.singleton_append] using
        ih (symbol :: result) ((state.1.1, some symbol), state.2)

/-- The actual `done` statement halts one transition after reversal completes. -/
theorem reverseOutputHaltTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    (advance (TM2.step (program positive H)))^[output.length + 2]
      (some ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩) =
      some ⟨none, clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩ := by
  rw [show output.length + 2 = (output.length + 1) + 1 by omega,
    Function.iterate_succ_apply',
    reverseOutputTrace positive H vertex remaining oldTable output countSuffix result state]
  exact doneStep positive H
    (boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result))
    (clearRegister state)

def reverseOutputHaltInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩
      (some ⟨none, clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩)
      (output.length + 2) where
  steps := output.length + 2
  evals_in_steps := reverseOutputHaltTrace positive H vertex remaining oldTable output countSuffix result state
  steps_le_m := Nat.le_refl _

end MaxCutGames.Foundations.Complexity.MachineExpanderTable

/-!
# Complete finite machine execution for the next expander table

The initialized old table and unary vertex count are consumed by one actual
finite program. The machine writes precisely the complete square/zigzag
rotation table, preserving its old table and all promised framing. The bound
is quadratic in the unary old-table length for each fixed small graph.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderTable

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

def completeBudget {v d : Nat} (G : Table v (degree d)) (H : Table (cloudSize d) d) : Nat :=
  1 + vertexLoopBudget G v + ((encodeWords (rotationWords (step G H))).length + 2)

theorem vertices_le_word_length {v d : Nat} (positive : 0 < d)
    (G : Table v (degree d)) : v ≤ (oldTableWord G).length := by
  have hq : 1 ≤ degree d := Nat.mul_pos positive positive
  have hv : v ≤ v * degree d := by simpa using Nat.mul_le_mul_left v hq
  have hr : v * degree d ≤ (oldTableWord G).length := by
    simp only [oldTableWord, encodeWords_length, rotationWords_length]
    omega
  exact hv.trans hr

/-- All actual loop, row, and final reversal costs are bounded quadratically. -/
theorem completeBudget_le {v d : Nat} (positive : 0 < d)
    (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    completeBudget G H ≤ (timePolynomial d).eval (oldTableWord G).length := by
  let L := (oldTableWord G).length
  let M := rowFactor d
  have vBound : v ≤ L + 1 := (vertices_le_word_length positive G).trans (Nat.le_succ L)
  have emitBound : 80 * (L + 1) + 2 ≤ 82 * (L + 1) := by omega
  have bodyBound : vertexBodyBudget G + 1 ≤ (82 * M + 1) * (L + 1) := by
    have mulBound := Nat.mul_le_mul_left M emitBound
    change M * (80 * (L + 1) + 2) + 1 ≤ _
    nlinarith
  have iterations := Nat.mul_le_mul vBound bodyBound
  have loopBound : v * (vertexBodyBudget G + 1) ≤ (82 * M + 1) * (L + 1)^2 := by
    calc
      _ ≤ (L + 1) * ((82 * M + 1) * (L + 1)) := iterations
      _ = _ := by ring
  have rowBound : v * M ≤ M * (L + 1) := by
    simpa only [Nat.mul_comm v M] using Nat.mul_le_mul_left M vBound
  have rowSuccBound : v * M + 1 ≤ (M + 1) * (L + 1) := by nlinarith
  have productBound := Nat.mul_le_mul rowBound rowSuccBound
  have lengthBound : (encodeWords (rotationWords (step G H))).length ≤
      M * (M + 1) * (L + 1)^2 := by
    calc
      _ ≤ (v * M) * (v * M + 1) := by
        simpa only [generatedWords_eq_rotationWords] using encode_generatedWords_length_le G H
      _ ≤ (M * (L + 1)) * ((M + 1) * (L + 1)) := productBound
      _ = _ := by ring
  have oneBound : 1 ≤ (L + 1)^2 := by nlinarith
  have combined := Nat.add_le_add loopBound lengthBound
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  change completeBudget G H ≤ (M * (M + 1) + 82 * M + 5) * (L + 1)^2
  unfold completeBudget vertexLoopBudget
  nlinarith

structure TableRun {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (state : State ρ d) (suffix : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  position_zero : finalState.2 = zeroPosition positive
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H))
    ⟨some (.inr .initialize_), state, initialTapes v (oldTableWord G) suffix⟩
    (some ⟨none, finalState,
      finalTapes v (oldTableWord G) (encodeWords (rotationWords (step G H))) suffix⟩)
    ((timePolynomial d).eval (oldTableWord G).length)

end MaxCutGames.Foundations.Complexity.MachineExpanderTable

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

theorem boundaryTapes_eq_cycleTapes (remaining current : Nat) (word suffix : List Bool) :
    boundaryTapes remaining current word suffix =
      cycleTapes remaining word (encodeWord current) [] [] [] suffix := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> rfl
  · cases tape <;> rfl

def copyFrame (remaining current : Nat) (word suffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes (MachineExpanderTable.initialTapes current word [])
    (extraFrame remaining current suffix)

def returnFrame (remaining current : Nat) (oldWord newWord suffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes (MachineExpanderTable.finalTapes current oldWord newWord [])
    (extraFrame remaining current suffix)

def installedFrame (remaining current : Nat) (newWord suffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  cycleTapes remaining newWord [] (encodeWord current) (encodeWord 0) [] suffix

def multipliedFrame (d remaining current : Nat) (newWord suffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  cycleTapes remaining newWord (encodeWord (cloudSize d * current))
    (encodeWord current) (encodeWord 0) [] suffix

theorem copyFrame_eq_cycleTapes (remaining current : Nat) (word suffix : List Bool) :
    copyFrame remaining current word suffix =
      cycleTapes remaining word (encodeWord current) [] (encodeWord current) [] suffix := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> simp [copyFrame, MachineEmbedding.tapes,
        MachineExpanderTable.initialTapes, MachineExpanderTable.extraTapes,
        cycleTapes, fromBoolTapes, boolWord, cycleWords]
  · cases tape <;> rfl

theorem returnFrame_eq_cycleTapes (remaining current : Nat)
    (oldWord newWord suffix : List Bool) :
    returnFrame remaining current oldWord newWord suffix =
      cycleTapes remaining oldWord (encodeWord current) (encodeWord current)
        (encodeWord 0) newWord suffix := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> simp [returnFrame, MachineEmbedding.tapes,
        MachineExpanderTable.finalTapes, MachineExpanderTable.boundaryTapes,
        MachineExpanderTable.extraTapes, cycleTapes, fromBoolTapes, boolWord, cycleWords]
  · cases tape <;> rfl

theorem copyFrame_eq_update (remaining current : Nat) (word suffix : List Bool) :
    Function.update (boundaryTapes remaining current word suffix)
      vertexCountTape (encodeWord current) = copyFrame remaining current word suffix := by
  rw [boundaryTapes_eq_cycleTapes, copyFrame_eq_cycleTapes]
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> rfl
  · cases tape <;> rfl

theorem multipliedFrame_eq_update (d remaining current : Nat) (word suffix : List Bool) :
    Function.update (installedFrame remaining current word suffix)
      (.inr .currentSize) (encodeWord (cloudSize d * current)) =
      multipliedFrame d remaining current word suffix := by
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> rfl
  · cases tape <;> rfl

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

/-!
# Bounds for materializing the actual expander family

The costs use the encoded old and new rotation tables, and the already checked
table-machine polynomial. The finite sum follows the actual recursive table
family. These arithmetic lemmas introduce no execution assumptions and make no
claim that the output is polynomial in an isolated binary level parameter.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamilyBounds

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

theorem resizeSum_succ {d : Nat} (H : Table (cloudSize d) d) (level : Nat) :
    resizeSum H (level + 1) = resizeSum H level + resizeCost (family H level) H := by
  simp only [resizeSum, Finset.sum_range_succ]

end MaxCutGames.Foundations.Complexity.MachineExpanderFamilyBounds

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineExpanderFamilyCycle
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

theorem installed_returnFrame (remaining current : Nat) (oldWord newWord suffix : List Bool) :
    fromBoolTapes (installedTapes (toBoolTapes (returnFrame remaining current oldWord newWord suffix))
      newWord) = installedFrame remaining current newWord suffix := by
  rw [returnFrame_eq_cycleTapes, toBool_cycleTapes]
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> rfl
  · cases tape <;> rfl

theorem cleaned_multipliedFrame (d remaining current : Nat) (newWord suffix : List Bool) :
    fromBoolTapes (cleanedCounterTapes
      (toBoolTapes (multipliedFrame d remaining current newWord suffix))) =
      boundaryTapes remaining (current * cloudSize d) newWord suffix := by
  rw [boundaryTapes_eq_cycleTapes]
  unfold multipliedFrame
  rw [toBool_cycleTapes]
  have multiply : cloudSize d * current = current * cloudSize d := Nat.mul_comm _ _
  rw [multiply]
  funext tape
  rcases tape with tape | tape
  · rcases tape with row | extra
    · cases row <;> rfl
    · cases extra <;> rfl
  · cases tape <;> rfl

structure ResizeRun {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (G : Table v (degree d)) (remaining : Nat) (state : State ρ d) (suffix : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
    ⟨some (.inr (.affine .copyCount .seed)), state,
      boundaryTapes remaining v (MachineExpanderTable.oldTableWord G) suffix⟩
    (some ⟨some (.inr .levelGuard), finalState,
      boundaryTapes remaining (v * cloudSize d)
        (encodeWords (rotationWords (step G H))) suffix⟩)
    (resizeCost G H)

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

/-- The guard changes only the physical remaining-level word. -/
theorem boundaryTapes_update_level (remaining current next : Nat)
    (word suffix : List Bool) :
    Function.update (boundaryTapes remaining current word suffix)
      (.inr .remainingLevel) (encodeWord next ++ suffix) =
      boundaryTapes next current word suffix := by
  funext tape
  rcases tape with tape | extra
  · rcases tape with row | extra
    · cases row <;> simp [boundaryTapes, tableFrame, MachineEmbedding.tapes, Function.update]
    · cases extra <;> simp [boundaryTapes, tableFrame, MachineEmbedding.tapes, Function.update]
  · cases extra <;> simp [boundaryTapes, extraFrame, MachineEmbedding.tapes, Function.update]

/-- The two literal prefixes install the actual level-zero table and unary one. -/
theorem initialTapes_initialize (level : Nat) (suffix : List Bool) :
    Function.update
      (Function.update (initialTapes level suffix) tableTape (initialEncoding d))
      (.inr .currentSize) (encodeWord 1) =
      boundaryTapes level 1 (initialEncoding d) suffix := by
  funext tape
  rcases tape with tape | extra
  · rcases tape with row | extra
    · cases row <;> simp [initialTapes, boundaryTapes, tableFrame,
        MachineEmbedding.tapes, Function.update, tableTape]
    · cases extra <;> simp [initialTapes, boundaryTapes, tableFrame,
        MachineEmbedding.tapes, Function.update, tableTape]
  · cases extra <;> simp [initialTapes, boundaryTapes, extraFrame,
      MachineEmbedding.tapes, Function.update, tableTape]

variable [Fintype ρ]

/-- Static alphabet transport preserves this actual single transition. -/
theorem actualStep_of_boolStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d)
    (start finish : TM2.Cfg BoolAlphabet (Label d) (State ρ d))
    (run : TM2.step (boolView positive H growth) start = some finish) :
    TM2.step (program positive H growth)
      (MachineAlphabetTransport.configuration alphabet_eq.symm start) =
      some (MachineAlphabetTransport.configuration alphabet_eq.symm finish) := by
  have h := MachineAlphabetTransport.step_simulation alphabet_eq.symm
    (boolView positive H growth) start
  rw [run] at h
  simpa only [boolView, MachineAlphabetTransport.program_symm_roundtrip,
    Option.map_some] using h

theorem bool_initializeStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d) :
    TM2.step (boolView positive H growth) ⟨some (.inr .initialize_), state, base⟩ =
      some ⟨some (.inr .levelGuard), normalizeState positive H state,
        Function.update
          (Function.update base tableTape (initialEncoding d ++ base (.inl (.inl .table))))
          (.inr .currentSize) (encodeWord 1 ++ base (.inr .currentSize))⟩ := by
  change some (TM2.stepAux (boolView positive H growth (.inr .initialize_)) state base) = _
  rw [boolView_outer]
  simp only [boolOuterStatement, Reduction.MachineSubstitution.stepAux_pushWord,
    List.reverse_reverse, TM2.stepAux]
  rfl

theorem bool_levelGuard_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d)
    (remaining : Nat) (suffix : List Bool)
    (counter : base (.inr .remainingLevel) = encodeWord (remaining + 1) ++ suffix) :
    TM2.step (boolView positive H growth) ⟨some (.inr .levelGuard), state, base⟩ =
      some ⟨some (.inr (.affine .copyCount .seed)), clearRegister state,
        Function.update base (.inr .remainingLevel) (encodeWord remaining ++ suffix)⟩ := by
  change some (TM2.stepAux (boolView positive H growth (.inr .levelGuard)) state base) = _
  rw [boolView_outer]
  simp [boolOuterStatement, MachineControl.statement, MachineUnaryCounter.guard,
    TM2.stepAux, registerStates, clearRegister, MachineExpanderTable.clearRegister,
    counter, encodeWord, List.replicate_succ]

theorem bool_levelGuard_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d)
    (suffix : List Bool)
    (counter : base (.inr .remainingLevel) = encodeWord 0 ++ suffix) :
    TM2.step (boolView positive H growth) ⟨some (.inr .levelGuard), state, base⟩ =
      some ⟨some (.inr .done), clearRegister state, base⟩ := by
  change some (TM2.stepAux (boolView positive H growth (.inr .levelGuard)) state base) = _
  rw [boolView_outer]
  simp [boolOuterStatement, MachineControl.statement, MachineUnaryCounter.guard,
    TM2.stepAux, registerStates, clearRegister, MachineExpanderTable.clearRegister,
    counter, encodeWord]

theorem bool_doneStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : Tape → List Bool) (state : State ρ d) :
    TM2.step (boolView positive H growth) ⟨some (.inr .done), state, base⟩ =
      some ⟨none, normalizeState positive H state, base⟩ := by
  change some (TM2.stepAux (boolView positive H growth (.inr .done)) state base) = _
  rw [boolView_outer]
  rfl

/-- The literal initialization executes in one transition of the actual program. -/
theorem initializeStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H growth) ⟨some (.inr .initialize_), state, base⟩ =
      some ⟨some (.inr .levelGuard), normalizeState positive H state,
        Function.update
          (Function.update base tableTape (initialEncoding d ++ base (.inl (.inl .table))))
          (.inr .currentSize) (encodeWord 1 ++ base (.inr .currentSize))⟩ := by
  have h := actualStep_of_boolStep positive H growth _ _
    (bool_initializeStep positive H growth (toBoolTapes base) state)
  simp only [configuration_fromBool, fromBoolTapes_update, fromBool_toBool] at h
  exact h

/-- A positive level physically loses one true bit, retaining its delimiter and suffix. -/
theorem levelGuard_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (remaining : Nat) (suffix : List Bool)
    (counter : base (.inr .remainingLevel) = encodeWord (remaining + 1) ++ suffix) :
    TM2.step (program positive H growth) ⟨some (.inr .levelGuard), state, base⟩ =
      some ⟨some (.inr (.affine .copyCount .seed)), clearRegister state,
        Function.update base (.inr .remainingLevel) (encodeWord remaining ++ suffix)⟩ := by
  have h := actualStep_of_boolStep positive H growth _ _
    (bool_levelGuard_succStep positive H growth (toBoolTapes base) state
      remaining suffix counter)
  simpa only [configuration_fromBool, fromBoolTapes_update, fromBool_toBool,
    boolWord] using h

/-- The zero delimiter is retained when the family loop enters its final halt. -/
theorem levelGuard_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (suffix : List Bool)
    (counter : base (.inr .remainingLevel) = encodeWord 0 ++ suffix) :
    TM2.step (program positive H growth) ⟨some (.inr .levelGuard), state, base⟩ =
      some ⟨some (.inr .done), clearRegister state, base⟩ := by
  have h := actualStep_of_boolStep positive H growth _ _
    (bool_levelGuard_zeroStep positive H growth (toBoolTapes base) state suffix counter)
  simpa only [configuration_fromBool, fromBool_toBool] using h

theorem doneStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H growth) ⟨some (.inr .done), state, base⟩ =
      some ⟨none, normalizeState positive H state, base⟩ := by
  have h := actualStep_of_boolStep positive H growth _ _
    (bool_doneStep positive H growth (toBoolTapes base) state)
  simpa only [configuration_fromBool, fromBool_toBool] using h

theorem initialize_boundaryStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (level : Nat) (suffix : List Bool) (state : State ρ d) :
    TM2.step (program positive H growth)
      ⟨some (.inr .initialize_), state, initialTapes level suffix⟩ =
      some ⟨some (.inr .levelGuard), initialState positive H (caller state),
        boundaryTapes level 1 (initialEncoding d) suffix⟩ := by
  have h := initializeStep positive H growth (initialTapes level suffix) state
  have ht : initialTapes level suffix (.inl (.inl .table)) = [] := rfl
  have hc : initialTapes level suffix (.inr .currentSize) = [] := rfl
  simp only [ht, hc, List.append_nil, normalizeState] at h
  exact h.trans (congrArg
    (fun tapes : ∀ tape, List (Alphabet tape) =>
      (some ⟨some (.inr .levelGuard), initialState positive H (caller state), tapes⟩ :
        Option (TM2.Cfg Alphabet (Label d) (State ρ d))))
    (initialTapes_initialize level suffix))

theorem levelGuard_boundary_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (remaining current : Nat)
    (word suffix : List Bool) (state : State ρ d) :
    TM2.step (program positive H growth)
      ⟨some (.inr .levelGuard), state, boundaryTapes (remaining + 1) current word suffix⟩ =
      some ⟨some (.inr (.affine .copyCount .seed)), clearRegister state,
        boundaryTapes remaining current word suffix⟩ := by
  simpa only [boundaryTapes_update_level] using
    levelGuard_succStep positive H growth
      (boundaryTapes (remaining + 1) current word suffix) state remaining suffix rfl

theorem levelGuard_boundary_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (current : Nat)
    (word suffix : List Bool) (state : State ρ d) :
    TM2.step (program positive H growth)
      ⟨some (.inr .levelGuard), state, boundaryTapes 0 current word suffix⟩ =
      some ⟨some (.inr .done), clearRegister state,
        boundaryTapes 0 current word suffix⟩ :=
  levelGuard_zeroStep positive H growth
    (boundaryTapes 0 current word suffix) state suffix rfl

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

/-! Actual counted repetition of complete table-expansion cycles. The input
counter is physically decremented, and the invariant carries the exact table
at the completed family level. -/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

noncomputable def levelLoopCost {d : Nat} (H : Table (cloudSize d) d) : Nat → Nat → Nat
  | _, 0 => 1
  | start, remaining + 1 => 1 + resizeCost (family H start) H +
      levelLoopCost H (start + 1) remaining

theorem levelLoopCost_prefix {d : Nat} (H : Table (cloudSize d) d) (start remaining : Nat) :
    levelLoopCost H start remaining + resizeSum H start =
      resizeSum H (start + remaining) + remaining + 1 := by
  induction remaining generalizing start with
  | zero => simp [levelLoopCost, Nat.add_comm]
  | succ remaining ih =>
      have h := ih (start + 1)
      rw [resizeSum_succ] at h
      have index : start + 1 + remaining = start + (remaining + 1) := by omega
      rw [index] at h
      simp only [levelLoopCost]
      omega

theorem levelLoopCost_zero_start {d : Nat} (H : Table (cloudSize d) d) (remaining : Nat) :
    levelLoopCost H 0 remaining = resizeSum H remaining + remaining + 1 := by
  simpa only [resizeSum_zero, Nat.add_zero, Nat.zero_add] using
    levelLoopCost_prefix H 0 remaining

def levelLoopTapes {d : Nat} (H : Table (cloudSize d) d)
    (completed remaining : Nat) (suffix : List Bool) : ∀ tape, List (Alphabet tape) :=
  boundaryTapes remaining (vertexCount (degree d) completed)
    (encodeWords (rotationWords (family H completed))) suffix

structure LevelLoopRun {d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (completed remaining : Nat) (state : State ρ d) (suffix : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
    ⟨some (.inr .levelGuard), state, levelLoopTapes H completed remaining suffix⟩
    (some ⟨some (.inr .done), finalState, familyTapes H (completed + remaining) suffix⟩)
    (levelLoopCost H completed remaining)

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineDummyRows
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual finite control for the dummy self-loop rows of one padded vertex.
The port count is a fixed program parameter. Vertex and reverse-dart indices
remain on unary tapes, and each row advances the reverse index by one actual
push. The all-true relation is a fixed literal field, initialized once.
-/

namespace MaxCutGames.Foundations.Complexity.MachineDummyRows

open Turing
open PCP.GraphTables
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

def trueBits : List Bool := encodeWords (relationWords trueRelation)

theorem trueBits_length : trueBits.length = 8192 := by
  simp only [trueBits, encodeWords_length, relationWords, trueRelation,
    Vector.toList_replicate, List.map_replicate, List.sum_replicate_nat,
    List.length_replicate] ; rfl

def rowBits (v e : Nat) : List Bool := encodeWord v ++ encodeWord e ++ trueBits

theorem rowBits_length (v e : Nat) : (rowBits v e).length = v + e + 8194 := by
  simp [rowBits, trueBits_length, encodeWord_length]
  omega

theorem rowBits_eq_graph_row {n m : Nat} (v : Fin n) (e : Fin m) :
    rowBits v.val e.val = encodeWords (rowWords (⟨v, e, trueRelation⟩ : DartRow n m)) := by
  rw [MachineTableRows.rowBits_eq]
  rfl

/-- Ordered serialized rows with successive physically stored reverse indices. -/
def rowsBits (v e : Nat) : Nat → List Bool
  | 0 => []
  | count + 1 => rowBits v e ++ rowsBits v (e + 1) count

variable {σ : Type}

/-- No input-dependent natural number occurs in the finite program. -/
def program (d : Nat) : Label d → TM2.Stmt Alphabet (Label d) (σ × Option Bool)
  | .inl () => pushWord 2 trueBits.reverse
      (.load (fun state => (state.1, none)) (continueAt (entry d)))
  | .inr (p, .inl stage) => MachineTableRows.routine fields 3 4 5
      (rowLabel p) (some (bumpLabel p)) stage
  | .inr (p, .inr ()) => .push 1 (fun _ => true) (continueAt (afterPort p))

/-- The three unary row fields, two empty work tapes, and accumulated output. -/
def fieldTapes (v e : Nat) (output : List Bool) : Fin 6 → List Bool :=
  ![encodeWord v, encodeWord e, trueBits, [], output, []]

/-- Before initialization, the fixed-relation tape is empty. -/
def initialTapes (v e : Nat) (output : List Bool) : Fin 6 → List Bool :=
  Function.update (fieldTapes v e output) 2 []

/-- The fixed literal relation is actually emitted by a finite push chain. -/
theorem initializeStep (d v e : Nat) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program d) ⟨some (start d), (ambient, register), initialTapes v e output⟩ =
      some ⟨entry d, (ambient, none), fieldTapes v e output⟩ := by
  change some (TM2.stepAux (program d (start d)) (ambient, register)
    (initialTapes v e output)) = _
  simp only [start, program, stepAux_pushWord, List.reverse_reverse, TM2.stepAux,
    initialTapes, Function.update_self, List.append_nil, Function.update_idem]
  have ht : Function.update (fieldTapes v e output) 2 trueBits = fieldTapes v e output := by
    funext i
    fin_cases i <;> simp [fieldTapes]
  rw [ht, stepAux_continueAt]

theorem rowTrace {d : Nat} (p : Fin d) (v e : Nat) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[
        4 * (v + e + 8194) + 2 * output.length + 9]
      (some ⟨some (rowLabel p .relationRead), (ambient, register), fieldTapes v e output⟩) =
      some ⟨some (bumpLabel p), (ambient, none), fieldTapes v e (output ++ rowBits v e)⟩ := by
  have hfields (i : Fin 3) : fields i ≠ (3 : Fin 6) ∧ fields i ≠ (5 : Fin 6) := by
    fin_cases i <;> decide
  have h := MachineTableRows.appendTrace fields (3 : Fin 6) 4 5 hfields
    (by decide) (by decide) (by decide) (rowLabel p) (some (bumpLabel p))
    (program d) (fun _ => rfl) (fieldTapes v e output) rfl rfl ambient register
  have hbits : MachineTableRows.fieldBits fields (fieldTapes v e output) = rowBits v e := by
    rfl
  have hsize : MachineTableRows.fieldSize fields (fieldTapes v e output) = v + e + 8194 := by
    rw [← MachineTableRows.fieldBits_length, hbits, rowBits_length]
  have ht : Function.update (fieldTapes v e output) 4 (output ++ rowBits v e) =
      fieldTapes v e (output ++ rowBits v e) := by
    funext i
    fin_cases i <;> simp [fieldTapes]
  simpa only [hsize, hbits, show fieldTapes v e output 4 = output from rfl, ht] using h

/-- The reverse index advances by pushing a real unary bit. The delimiter,
all input fields, output, and work tapes have their exact stated contents. -/
theorem bumpStep {d : Nat} (p : Fin d) (v e : Nat) (output : List Bool) (ambient : σ) :
    TM2.step (program d) ⟨some (bumpLabel p), (ambient, none), fieldTapes v e output⟩ =
      some ⟨afterPort p, (ambient, none), fieldTapes v (e + 1) output⟩ := by
  change some (TM2.stepAux (program d (bumpLabel p)) (ambient, none)
    (fieldTapes v e output)) = _
  simp only [bumpLabel, program, TM2.stepAux]
  rw [stepAux_continueAt]
  congr 2
  funext i
  fin_cases i <;> simp [fieldTapes, encodeWord, List.replicate_succ]

/-- The concrete row body and its actual index increment are consecutive
phases of one fixed program; no whole-body trace is supplied as a premise. -/
theorem rowAndBumpTrace {d : Nat} (p : Fin d) (v e : Nat) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[
        4 * (v + e + 8194) + 2 * output.length + 10]
      (some ⟨some (rowLabel p .relationRead), (ambient, register), fieldTapes v e output⟩) =
      some ⟨afterPort p, (ambient, none), fieldTapes v (e + 1) (output ++ rowBits v e)⟩ := by
  rw [show 4 * (v + e + 8194) + 2 * output.length + 10 =
      (4 * (v + e + 8194) + 2 * output.length + 9) + 1 by omega,
    Function.iterate_succ_apply', rowTrace, MachineComposition.advance_some]
  exact bumpStep p v e (output ++ rowBits v e) ambient

/-- Exact sum of actual row-and-increment costs. This recurrence is matched
to the program by `suffixTrace`, rather than postulated as a runtime. -/
def steps (v e : Nat) (output : List Bool) : Nat → Nat
  | 0 => 0
  | count + 1 => (4 * (v + e + 8194) + 2 * output.length + 10) +
      steps v (e + 1) (output ++ rowBits v e) count

/-- Actual execution from any port boundary to the final halt. The finite
control index fixes the remaining number of rows; all unbounded values are
physically stored in `fieldTapes`. -/
theorem suffixTrace {d : Nat} (count : Nat) (p : Fin d) (hp : p.val + count = d)
    (v e : Nat) (output : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[steps v e output count]
      (some ⟨some (rowLabel p .relationRead), (ambient, register), fieldTapes v e output⟩) =
      some ⟨none, (ambient, none), fieldTapes v (e + count) (output ++ rowsBits v e count)⟩ := by
  induction count generalizing p v e output register with
  | zero =>
    have hlt := p.isLt
    omega
  | succ count ih =>
    rw [steps, Nat.add_comm (4 * (v + e + 8194) + 2 * output.length + 10),
      Function.iterate_add_apply, rowAndBumpTrace]
    by_cases hc : count = 0
    · subst count
      have hlast : ¬ p.val + 1 < d := by omega
      simp [afterPort, hlast, steps, rowsBits]
    · have hnext : p.val + 1 < d := by omega
      rw [afterPort, dite_eq_left hnext]
      have hh := ih ⟨p.val + 1, hnext⟩ (by change (p.val + 1) + count = d; omega)
        v (e + 1) (output ++ rowBits v e) none
      have he : (e + 1) + count = e + (count + 1) := by omega
      simpa only [rowsBits, List.append_assoc, he] using hh

/-- One fixed-relation initialization transition followed by all actual rows.
At zero ports initialization itself halts; no row is spuriously produced. -/
theorem allTrace (d v e : Nat) (output : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[steps v e output d + 1]
      (some ⟨some (start d), (ambient, register), initialTapes v e output⟩) =
      some ⟨none, (ambient, none), fieldTapes v (e + d) (output ++ rowsBits v e d)⟩ := by
  rw [Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step (program d)))^[steps v e output d]
    (TM2.step (program d) ⟨some (start d), (ambient, register), initialTapes v e output⟩) = _
  rw [initializeStep]
  by_cases hd : 0 < d
  · rw [entry, dite_eq_left hd]
    exact suffixTrace d ⟨0, hd⟩ (by simp) v e output ambient none
  · have hz : d = 0 := by omega
    subst d
    simp [entry, steps, rowsBits]

/-- Every actual row cost is bounded by the largest row and accumulated
output encountered during this finite loop. -/
theorem steps_le_bound (v e : Nat) (output : List Bool) (count : Nat) :
    steps v e output count ≤ count *
      (4 * (v + e + count + 8194) +
        2 * (output.length + count * (v + e + count + 8194)) + 10) := by
  induction count generalizing e output with
  | zero => simp [steps]
  | succ count ih =>
    let B := v + e + (count + 1) + 8194
    let C := 4 * B + 2 * (output.length + (count + 1) * B) + 10
    have hb : v + (e + 1) + count + 8194 = B := by dsimp [B]; omega
    have hi := ih (e + 1) (output ++ rowBits v e)
    rw [List.length_append, rowBits_length, hb] at hi
    have hrow : v + e + 8194 ≤ B := by dsimp [B]; omega
    have hout : output.length + (v + e + 8194) + count * B ≤
        output.length + (count + 1) * B := by
      calc
        _ ≤ output.length + B + count * B :=
          Nat.add_le_add_right (Nat.add_le_add_left hrow output.length) _
        _ = _ := by simp only [Nat.add_mul, Nat.one_mul]; omega
    have hconstant : 4 * B + 2 * (output.length + (v + e + 8194) + count * B) + 10 ≤ C := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hout) (4 * B)) 10
    have hremaining := hi.trans (Nat.mul_le_mul_left count hconstant)
    have hbody : 4 * (v + e + 8194) + 2 * output.length + 10 ≤ C := by
      exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 4 hrow)
        (Nat.mul_le_mul_left 2 (Nat.le_add_right output.length ((count + 1) * B)))) 10
    change (4 * (v + e + 8194) + 2 * output.length + 10) +
      steps v (e + 1) (output ++ rowBits v e) count ≤ (count + 1) * C
    calc
      _ ≤ C + count * C := Nat.add_le_add hbody hremaining
      _ = (count + 1) * C := by rw [Nat.add_mul, Nat.one_mul]; omega

end MaxCutGames.Foundations.Complexity.MachineDummyRows

/-!
# Actual inherited-row emission for a dummy vertex

The fixed program preserves the physical unary vertex index on tape zero,
computes its inherited reverse index on tape one, invokes the actual one-port
dummy-row emitter, and drains the computed index and fixed true relation.
Tape four accumulates output. Tapes one, two, three, and five are empty at both
boundaries. The degree is fixed program data, not an input-dependent control
parameter.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingPaddingWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact serialization of whole-vertex padding

The original dart rows remain in their original order, with every old tail,
reverse index, and relation bit unchanged. The suffix is exactly the bit stream
emitted by the checked dummy-vertex machine, starting at vertex `n` and dart
`n*d`. This is an equality for the actual table codec, with no runtime premise.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingPaddingWords

open Complexity PortTables

variable {n m d : Nat}

/-- The bits of one actual table row, in the existing graph codec. -/
def rowBits (table : Table n d) (v : Fin n) (p : Fin d) : List Bool :=
  encodeWord v.val ++ encodeWord (table.reverseIndex[rowIndex n d (v, p)]).val ++
    encodeWords (GraphTables.relationWords table.relations[rowIndex n d (v, p)])

def vertexBits (table : Table n d) (v : Fin n) : List Bool :=
  (List.ofFn (fun p : Fin d => rowBits table v p)).flatten

/-- Every bit in an original row survives padding unchanged. -/
theorem rowBits_pad_old (table : Table n d) (h : n ≤ m) (v : Fin n) (p : Fin d) :
    rowBits (PreprocessingPaddingTables.pad table h) (v.castLE h) p = rowBits table v p := by
  unfold rowBits
  rw [PreprocessingPaddingTables.reverseIndex_pad_old,
    PreprocessingPaddingTables.relations_pad_old]
  have he : (rowIndex m d ((rotation table (v, p)).1.castLE h,
      (rotation table (v, p)).2)).val = (table.reverseIndex[rowIndex n d (v, p)]).val := by
    rw [← rowIndex_rotation]
    rfl
  rw [he]
  rfl

@[simp] theorem vertexBits_pad_old (table : Table n d) (h : n ≤ m) (v : Fin n) :
    vertexBits (PreprocessingPaddingTables.pad table h) (v.castLE h) = vertexBits table v := by
  simp only [vertexBits, rowBits_pad_old]

end MaxCutGames.Foundations.PCP.PreprocessingPaddingWords

/-!
# Complete serialization of the actual regularized table

Each global vertex emits its internal ports in increasing order, then its
inherited port. Original darts are the first global vertices. Dummy vertices
follow in increasing owner and local-dummy order. These are identities for the
actual stored rows and existing codec, with arbitrary actual cloud tables.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingRegularWords

open DegreeReplacement PreprocessingCloudIndex PreprocessingRegularTables Complexity
open scoped BigOperators

variable (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)

/-- Read one row of the actual output, in the chosen global coordinates. -/
def actualRow (x : Vertex t padding) (p : Fin q ⊕ Unit) :
    GraphTables.DartRow (vertexCount t padding) (vertexCount t padding * (q + 1)) :=
  (PortTables.flatRows (ofCloudTables t padding tables))[
    PortTables.rowIndex _ _ (vertexOrder t padding x, portOrder q p)]

theorem actualRow_eq (x : Vertex t padding) (p : Fin q ⊕ Unit) :
    actualRow t padding tables x p =
      ⟨vertexOrder t padding x,
        (ofCloudTables t padding tables).reverseIndex[
          PortTables.rowIndex _ _ (vertexOrder t padding x, portOrder q p)],
        (ofCloudTables t padding tables).relations[
          PortTables.rowIndex _ _ (vertexOrder t padding x, portOrder q p)]⟩ := by
  simp only [actualRow, PortTables.flatRows, Vector.getElem_ofFn,
    Fin.getElem_fin, Fin.eta, Equiv.symm_apply_apply]

@[simp] theorem actualRow_tail (x : Vertex t padding) (p : Fin q ⊕ Unit) :
    (actualRow t padding tables x p).tail.val = (vertexOrder t padding x).val := by
  rw [actualRow_eq]

@[simp] theorem inherited_original_reverse (e : Fin t.darts) :
    (actualRow t padding tables (.inl e) (.inr ())).reverseIndex.val =
      (q + 1) * t.rows[e].reverseIndex.val + q := by
  rw [actualRow_eq]
  change ((ofCloudTables t padding tables).reverseIndex[PortTables.rowIndex _ _
    (vertexOrder t padding (.inl e), portOrder q (.inr ()))]).val = _
  rw [← PortTables.rowIndex_rotation, rotation_ofCloudTables]
  change (PortTables.rowIndex _ _
    (vertexOrder t padding (.inl (GraphTables.reverseAt t.rows e)), portOrder q (.inr ()))).val = _
  rw [PortTables.rowIndex_val, vertexOrder_original, portOrder_inherited]
  exact Nat.add_comm _ _

@[simp] theorem inherited_dummy_reverse (v : Fin t.vertices) (j : Fin (padding v)) :
    (actualRow t padding tables (.inr ⟨v, j⟩) (.inr ())).reverseIndex.val =
      (q + 1) * (t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val) + q := by
  rw [actualRow_eq]
  change ((ofCloudTables t padding tables).reverseIndex[PortTables.rowIndex _ _
    (vertexOrder t padding (.inr ⟨v, j⟩), portOrder q (.inr ()))]).val = _
  rw [← PortTables.rowIndex_rotation, rotation_ofCloudTables]
  change (PortTables.rowIndex _ _
    (vertexOrder t padding (.inr ⟨v, j⟩), portOrder q (.inr ()))).val = _
  rw [PortTables.rowIndex_val, PreprocessingPaddingOffsets.vertexOrder_dummy_val,
    portOrder_inherited]
  exact Nat.add_comm _ _

@[simp] theorem inherited_original_relation (e : Fin t.darts) :
    (actualRow t padding tables (.inl e) (.inr ())).relation = t.rows[e].relation := by
  rw [actualRow_eq]
  apply relation_ext_inline_PreprocessingRegularWords
  intro a b
  exact accepts_original t padding tables e a b

@[simp] theorem inherited_dummy_relation (v : Fin t.vertices) (j : Fin (padding v)) :
    (actualRow t padding tables (.inr ⟨v, j⟩) (.inr ())).relation =
      MachineDummyRows.trueRelation := by
  rw [actualRow_eq]
  apply relation_ext_inline_PreprocessingRegularWords
  intro a b
  have h := accepts_dummy t padding tables ⟨v, j⟩ a b
  simpa only [PortTables.accepts, MachineDummyRows.trueRelation,
    GraphTables.relationAt, Fin.getElem_fin, Vector.getElem_replicate] using h

end MaxCutGames.Foundations.PCP.PreprocessingRegularWords

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineLazyTableRuntime
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical polynomial-time computation of the executable lazy preprocessing map.
The raw machine's retained original input is physically drained by the checked
canonical-output wrapper before it reaches the standard `haltList` endpoint.
-/

/-! The actual padding, expander overlay, and lazy-loop stages composed into
one polynomial-time finite machine. The initial degree-replacement stage is
assembled separately. -/

/-! The complete actual preprocessing machine, including degree replacement,
vertex padding, explicit expander construction, overlay, and lazy edges. -/

/-!
An actual logarithmic-round counter. Unary input is stripped to a raw tally;
each positive round emits one tally and halves the remaining input by pairing
symbols. The zero input emits one round explicitly. All tapes except the
canonical output are empty at termination.
-/

namespace MaxCutGames.Foundations.Complexity.MachineLogCounter

open Turing

theorem restoreTrace (n : Nat) (output : List Bool) (started : Bool) :
    next^[n + 1] (some (configuration (some 4) ((false, started), none)
      [] (List.replicate n true) output)) =
      some (configuration (some 2) ((false, started), none) (List.replicate n true) [] output) := by
  have run := Reduction.MachineTransfer.transferAt_fromTapes (1 : Fin 3) 0 (by decide)
    id false (4 : Fin 5) (some 2) program rfl
    (rawTapes [] (List.replicate n true) output) (false, started) none
  simp only [rawTapes, List.length_replicate, List.reverse_replicate, List.map_id,
    List.append_nil] at run
  have tapesEq : Reduction.MachineTransfer.tapesAt (1 : Fin 3) 0
      (rawTapes [] (List.replicate n true) output) [] (List.replicate n true) =
      rawTapes (List.replicate n true) [] output := by
    funext k
    fin_cases k <;> rfl
  rw [tapesEq] at run
  exact run

/-- The halving rounds are actual guard, scan, and restoration executions. -/
theorem coreTrace (n : Nat) (output : List Bool) (started : Bool) :
    next^[coreTime n] (some (configuration (some 2) ((false, started), none)
      (List.replicate n true) [] output)) =
      some (configuration none initialState [] []
        (List.replicate (increments n started) true ++ output)) := by
  induction n using Nat.strong_induction_on generalizing output started with
  | h n ih =>
    cases n with
    | zero =>
      cases started with
      | false => simpa [increments, next, MachineComposition.advance] using! guardStep_zero output false
      | true => simpa [increments, next, MachineComposition.advance] using! guardStep_zero output true
    | succ n =>
      have nonzero : n + 1 ≠ 0 := by omega
      have smaller : (n + 1) / 2 < n + 1 := by omega
      have recursive := ih ((n + 1) / 2) smaller (true :: output) true
      have half := halfTrace (n + 1) 0 (true :: output) false true none
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.zero_add,
        List.replicate_zero] at half
      have restore := restoreTrace ((n + 1) / 2) (true :: output) true
      rw [coreTime_positive nonzero]
      rw [show n + 1 + (n + 1) / 2 + 3 + coreTime ((n + 1) / 2) =
        (coreTime ((n + 1) / 2) + ((n + 1) / 2 + 1) + (n + 1 + 1)) + 1 by omega,
        Function.iterate_succ_apply]
      change next^[coreTime ((n + 1) / 2) + ((n + 1) / 2 + 1) + (n + 1 + 1)]
        (machine.step (configuration (some 2) ((false, started), none)
          (List.replicate (n + 1) true) [] output)) = _
      rw [guardStep_positive, Function.iterate_add_apply, half,
        Function.iterate_add_apply, restore, recursive]
      rw [increments_half nonzero started]
      simp only [List.replicate_add, List.replicate_one, List.append_assoc, List.singleton_append]

end MaxCutGames.Foundations.Complexity.MachineLogCounter

/-! A fixed Boolean-stack program prepending the logarithmic round count to
a graph table. It copies the original word, adds its two unary header values,
runs the actual logarithm machine, then emits the counter and original word. -/

/-! Actual archive-copy and unary-header addition before the embedded logarithm
machine. The two header values stay on tapes; they never enter finite control. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_GraphCounterFinish
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual cleanup and emission of the counter followed by the preserved graph. -/

namespace MaxCutGames.Foundations.Complexity.GraphCounterFinish

open Turing GraphCounterModel

theorem drainTrace (rest original counter : List Bool) :
    (MachineComposition.advance (TM2.step program))^[rest.length + 1]
      (some ⟨some (.inr .clearInput), initialState, frame rest original counter [] []⟩) =
      some ⟨some (.inr .clockCopy), initialState, frame [] original counter [] []⟩ := by
  have h := (MachineDrain.drainInTime (Sum.inr ExtraTape.input) (Sum.inr ExtraLabel.clearInput)
    (some (.inr .clockCopy)) program rfl (frame rest original counter [] [])
    MachineLogCounter.initialState none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[rest.length + 1]
    (some ⟨some (.inr .clearInput), initialState, frame rest original counter [] []⟩) = _ at h
  have update : Function.update (frame rest original counter [] []) (.inr .input) [] =
      frame [] original counter [] [] := by
    funext tape
    cases tape with
    | inl i => simp [frame]
    | inr k => cases k <;> simp [frame]
  simpa only [update, initialState] using h

theorem clockCopyTrace (original counter : List Bool) :
    (MachineComposition.advance (TM2.step program))^[counter.length + 1]
      (some ⟨some (.inr .clockCopy), initialState, frame [] original counter [] []⟩) =
      some ⟨some (.inr .archiveCopy), initialState, frame [] original [] counter.reverse []⟩ := by
  have h := (Reduction.MachineTransfer.transferAtInTime (Sum.inl (2 : Fin 3))
    (Sum.inr ExtraTape.scratch) (by decide) id false (.inr .clockCopy)
    (some (.inr .archiveCopy)) program rfl (frame [] original counter [] [])
    MachineLogCounter.initialState none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[counter.length + 1]
    (some ⟨some (.inr .clockCopy), initialState, frame [] original counter [] []⟩) = _ at h
  have update : Reduction.MachineTransfer.tapesAt (Sum.inl (2 : Fin 3))
      (Sum.inr ExtraTape.scratch) (frame [] original counter [] []) []
        ((frame [] original counter [] [] (.inl 2)).reverse.map id ++
          frame [] original counter [] [] (.inr .scratch)) =
      frame [] original [] counter.reverse [] := by
    funext tape
    cases tape with
    | inl i => fin_cases i <;> simp [Reduction.MachineTransfer.tapesAt, frame]
    | inr k => cases k <;> simp [Reduction.MachineTransfer.tapesAt, frame]
  simpa only [update, initialState] using h

theorem archiveCopyTrace (original counter : List Bool) :
    (MachineComposition.advance (TM2.step program))^[original.length + 1]
      (some ⟨some (.inr .archiveCopy), initialState, frame [] original [] counter.reverse []⟩) =
      some ⟨some (.inr .finalReverse), initialState,
        frame [] [] [] (original.reverse ++ counter.reverse) []⟩ := by
  have h := (Reduction.MachineTransfer.transferAtInTime (Sum.inr ExtraTape.archive)
    (Sum.inr ExtraTape.scratch) (by decide) id false (.inr .archiveCopy)
    (some (.inr .finalReverse)) program rfl (frame [] original [] counter.reverse [])
    MachineLogCounter.initialState none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[original.length + 1]
    (some ⟨some (.inr .archiveCopy), initialState, frame [] original [] counter.reverse []⟩) = _ at h
  have update : Reduction.MachineTransfer.tapesAt (Sum.inr ExtraTape.archive)
      (Sum.inr ExtraTape.scratch) (frame [] original [] counter.reverse []) []
        ((frame [] original [] counter.reverse [] (.inr .archive)).reverse.map id ++
          frame [] original [] counter.reverse [] (.inr .scratch)) =
      frame [] [] [] (original.reverse ++ counter.reverse) [] := by
    funext tape
    cases tape with
    | inl i => simp [Reduction.MachineTransfer.tapesAt, frame]
    | inr k => cases k <;> simp [Reduction.MachineTransfer.tapesAt, frame]
  simpa only [update, initialState] using h

theorem reverseTrace (original counter : List Bool) :
    (MachineComposition.advance (TM2.step program))^[original.length + counter.length + 1]
      (some ⟨some (.inr .finalReverse), initialState,
        frame [] [] [] (original.reverse ++ counter.reverse) []⟩) =
      some (haltList machine (counter ++ original)) := by
  have h := (Reduction.MachineTransfer.transferAtInTime (Sum.inr ExtraTape.scratch)
    (Sum.inr ExtraTape.output) (by decide) id false (.inr .finalReverse) none program rfl
    (frame [] [] [] (original.reverse ++ counter.reverse) []) MachineLogCounter.initialState none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[
    (original.reverse ++ counter.reverse).length + 1]
    (some ⟨some (.inr .finalReverse), initialState,
      frame [] [] [] (original.reverse ++ counter.reverse) []⟩) = _ at h
  have update : Reduction.MachineTransfer.tapesAt (Sum.inr ExtraTape.scratch)
      (Sum.inr ExtraTape.output) (frame [] [] [] (original.reverse ++ counter.reverse) []) []
        ((frame [] [] [] (original.reverse ++ counter.reverse) [] (.inr .scratch)).reverse.map id ++
          frame [] [] [] (original.reverse ++ counter.reverse) [] (.inr .output)) =
      frame [] [] [] [] (counter ++ original) := by
    funext tape
    cases tape with
    | inl i => simp [Reduction.MachineTransfer.tapesAt, frame]
    | inr k => cases k <;> simp [Reduction.MachineTransfer.tapesAt, frame]
  rw [update] at h
  rw [← finish_eq]
  simpa only [List.length_append, List.length_reverse, initialState] using! h

theorem finishTrace (counter rest original : List Bool) :
    (MachineComposition.advance (TM2.step program))^[
        rest.length + 2 * counter.length + 2 * original.length + 4]
      (some (clockConfiguration (extraTapes rest original) none
        (haltList MachineLogCounter.machine counter))) =
      some (haltList machine (counter ++ original)) := by
  rw [start_eq]
  have total := trace_trans_inline_GraphCounterFinish _
    (trace_trans_inline_GraphCounterFinish _ (trace_trans_inline_GraphCounterFinish _ (drainTrace rest original counter)
      (clockCopyTrace original counter)) (archiveCopyTrace original counter))
    (reverseTrace original counter)
  simpa only [show rest.length + 1 + (counter.length + 1) + (original.length + 1) +
      (original.length + counter.length + 1) =
      rest.length + 2 * counter.length + 2 * original.length + 4 by omega] using total

def finishInTime (counter rest original : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      (clockConfiguration (extraTapes rest original) none (haltList MachineLogCounter.machine counter))
      (some (haltList machine (counter ++ original)))
      (rest.length + 2 * counter.length + 2 * original.length + 4) where
  steps := rest.length + 2 * counter.length + 2 * original.length + 4
  evals_in_steps := finishTrace counter rest original
  steps_le_m := le_rfl

end MaxCutGames.Foundations.Complexity.GraphCounterFinish

/-! A complete finite machine adding the actual logarithmic graph-round count
as a unary prefix, preserving every bit of the original validated graph table. -/

namespace MaxCutGames.Foundations.Complexity.GraphCounterPrefix

open Turing PCP GraphCounterModel GraphCounterFinish

def count (table : GraphTables.Table) : Nat := (table.vertices + table.darts).log2 + 1

end MaxCutGames.Foundations.Complexity.GraphCounterPrefix

/-!
Actual unary-guard iteration for a logarithmic number of rounds. Semantic
cardinality grows by a fixed linear factor. A separate encoding polynomial
bounds each intermediate word; it is never iterated as a size recurrence.
The body hypotheses are individual executions of the supplied finite program.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_RoundGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Size of the actual fixed amplification round

All constants below depend only on the fixed port alphabet and walk length.
The round itself is the checked preprocessing, powering, and alphabet graph
construction in `AmplificationRound`; no second graph constructor is introduced.
Closed constants are kept symbolic rather than evaluated.
-/

/-!
The actual finite graph iteration used by the mathematical PCP construction.
One fixed, explicitly supplied complete address list is shared by every round.
Each round constructs a new constraint graph. The scalar gap and size are the
actual minimum rejection fraction and actual finite cardinalities of that graph.

The final Boolean formula uses supplied vertex and dart numberings. These
theorems establish the finite objects and their size/gap properties, not a
machine running-time theorem or an independently encoded NP-hardness theorem.
-/

/-! The exact table-to-formula converter used by the final CNF machine.
Its semantic count premise is explicit; amplification supplies that premise
elsewhere. The converter chooses no vertex or dart numbering. -/

namespace MaxCutGames.Foundations.PCP.FinalTableFormula

open Target Complexity

theorem formulaBits_length_le_polynomial (table : GraphTables.Table) :
    (formulaBits (output table)).length ≤
      sizePolynomial.eval (GraphTables.tableBits table).length := by
  have hinput := GraphTableComplexity.size_add_two_le_bits table
  have hv : (output table).«variables» ≤ 36864 * (GraphTables.tableBits table).length := by
    rw [variable_count]
    omega
  have hc : (output table).clauses.length ≤ 40960 * (GraphTables.tableBits table).length := by
    rw [clause_count]
    omega
  have hsum : (output table).«variables» + (output table).clauses.length + 2 ≤
      77824 * (GraphTables.tableBits table).length + 2 := by omega
  have hproduct := Nat.mul_le_mul hc (Nat.mul_le_mul_left 3 (Nat.add_le_add_right hv 2))
  rw [sizePolynomial_eval]
  exact (formulaBits_length_le (output table)).trans (Nat.add_le_add hsum hproduct)

end MaxCutGames.Foundations.PCP.FinalTableFormula

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_TableIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iteration of the concrete stored-table round, with the original formula's
actual initial graph size controlling the number of rounds. -/

namespace MaxCutGames.Foundations.PCP.TableIteration

open RoundTables
open Target Complexity

def run (H : BaseTable) : Nat → Input → Input := AmplificationIteration.run (step H)

/-- The same data computation on all validated tables; positivity is an invariant,
and is erased from the runtime path. -/
def runTables (H : BaseTable) : Nat → GraphTables.Table → GraphTables.Table :=
  AmplificationIteration.run (build H)

theorem run_val (H : BaseTable) (n : Nat) (input : Input) :
    (run H n input).val = runTables H n input.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change build H (run H n input).val = build H (runTables H n input.val)
      rw [ih]

end MaxCutGames.Foundations.PCP.TableIteration

/-! Exact transport of powering through a change of ports. The target's actual
address selector is pulled back, so no compatibility of enumeration orders or
consistency restriction on raw padded labels is needed. -/

/-! Gap amplification for the actual numbered table round. The fixed base
expander is the only supplied construction datum with a spectral certificate. -/

/-! Both semantic implications for the actual stored-table 3SAT gap map.
The positive clause gap follows from the full actual repeated transformation.
The full map's polynomial-time machine is certified separately. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_GraphIterationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One polynomial bounds every actual intermediate encoding in the concrete
logarithmic graph iteration. The linear recurrence is on graph size. -/

namespace MaxCutGames.Foundations.Complexity.GraphIterationBounds

open PCP RoundTables

def inputBits (input : Input) : List Bool := GraphTables.tableBits input.val

def words (H : BaseTable) (input : Input) (i : Nat) : List Bool :=
  GraphTables.tableBits (TableIteration.runTables H i input.val)

def count (input : Input) : Nat := GraphCounterPrefix.count input.val

noncomputable def lengthPolynomial : Polynomial Nat :=
  (GraphTableComplexity.encodingPolynomial 64).comp (PCPIterationMachine.sizePolynomial sizeFactor)

theorem size_le_inputBits (input : Input) : size input ≤ (inputBits input).length := by
  have h := GraphTableComplexity.size_add_two_le_bits input.val
  unfold size inputBits
  omega

theorem intermediate_size (H : BaseTable) (input : Input) (i : Nat) (hi : i ≤ count input) :
    size (TableIteration.run H i input) ≤ PCPIterationMachine.sizeEnvelope sizeFactor (size input) := by
  apply PCPIterationMachine.semanticSize_bound
    (fun j => size (TableIteration.run H j input)) sizeFactor (size input)
    sizeFactor_positive (Nat.le_succ _) _ i hi
  intro j _
  exact step_size H (TableIteration.run H j input)

noncomputable def runtimePolynomial (bodyTime : Polynomial Nat) : Polynomial Nat :=
  (Polynomial.X + 1) * (bodyTime.comp lengthPolynomial + 2 * lengthPolynomial + 4) +
    2 * lengthPolynomial + 4

theorem runtimePolynomial_eval (bodyTime : Polynomial Nat) (N : Nat) :
    (runtimePolynomial bodyTime).eval N =
      (N + 1) * (bodyTime.eval (lengthPolynomial.eval N) + 2 * lengthPolynomial.eval N + 4) +
        2 * lengthPolynomial.eval N + 4 := by
  simp only [runtimePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_ofNat, Polynomial.eval_comp]

end MaxCutGames.Foundations.Complexity.GraphIterationBounds

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_ProductTarget
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Explicit numbered permutation-table outputs for bipartite graphs and products.
All numbering maps are supplied as actual equivalences; the product uses the
computable radix equivalence with division/remainder inverse, never an arbitrary
finite-type enumeration. The value bridge preserves every list occurrence.
-/

namespace MaxCutGames.Explicit.ProductTarget

open MaxCutGames.Foundations
open Target
open MachineOutputContract
open scoped BigOperators

variable {L R E : Type*} {q N M : ℕ}

theorem render_get (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (i : Fin (render G vertices edges tables hM).constraints.length) :
    (render G vertices edges tables hM).constraints[i] =
      row G vertices edges tables ⟨i.val, by simpa using i.isLt⟩ := by
  change (List.ofFn (row G vertices edges tables))[i.val]'(by simpa using i.isLt) = _
  exact List.getElem_ofFn (by simpa using i.isLt)

def render_simpleBipartite (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M) :
    SimpleBipartite (render G vertices edges tables hM) where
  side v := Sum.elim (fun _ => false) (fun _ => true) (vertices.symm v)
  sourceSide i := by simp only [render_get, row, Equiv.symm_apply_apply, Sum.elim_inl]
  targetSide i := by simp only [render_get, row, Equiv.symm_apply_apply, Sum.elim_inr]
  endpoints_injective := by
    intro i j hij
    have hi : i.val < M := by simpa using i.isLt
    have hj : j.val < M := by simpa using j.isLt
    have hrows :
        ((row G vertices edges tables ⟨i.val, hi⟩).source,
          (row G vertices edges tables ⟨i.val, hi⟩).target) =
        ((row G vertices edges tables ⟨j.val, hj⟩).source,
          (row G vertices edges tables ⟨j.val, hj⟩).target) := by
      simpa only [render_get] using! hij
    have hedge : edges ⟨i.val, hi⟩ = edges ⟨j.val, hj⟩ := by
      apply G.simple
      apply Prod.ext
      · exact Sum.inl.inj (vertices.injective (congrArg Prod.fst hrows))
      · exact Sum.inr.inj (vertices.injective (congrArg Prod.snd hrows))
    exact Fin.ext (congrArg (fun k : Fin M => k.val) (edges.injective hedge))

section Value

variable [Fintype L] [Fintype R] [Fintype E]

omit [Fintype L] [Fintype R] in
/-- A full vertex labeling pulls back to two independently local labelings. -/
theorem render_count (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (htable : ∀ e, permutationEquiv (tables e) = G.permutation e)
    (labeling : Fin N → Fin q) :
    countSatisfied labeling (render G vertices edges tables hM).constraints =
      G.satisfiedCount (fun x => labeling (vertices (Sum.inl x)))
        (fun y => labeling (vertices (Sum.inr y))) := by
  classical
  have ht (e : E) (a : Fin q) : (tables e).images[a] = G.permutation e a :=
    congrArg (fun p : Equiv.Perm (Fin q) => p a) (htable e)
  change countSatisfied labeling (List.ofFn (row G vertices edges tables)) = _
  rw [Integration.GapSemantics.countSatisfied_ofFn]
  unfold BipartiteGame.satisfiedCount
  apply Fintype.sum_equiv edges
  intro i
  simp [row, Constraint.satisfied, ht]

omit [Fintype L] [Fintype R] in
theorem render_count_merge (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (htable : ∀ e, permutationEquiv (tables e) = G.permutation e)
    (left : L → Fin q) (right : R → Fin q) :
    countSatisfied (mergeLabelings vertices left right)
      (render G vertices edges tables hM).constraints = G.satisfiedCount left right := by
  simpa only [mergeLabelings_left, mergeLabelings_right] using
    render_count G vertices edges tables hM htable (mergeLabelings vertices left right)

theorem render_maxSatisfied (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (htable : ∀ e, permutationEquiv (tables e) = G.permutation e) :
    Integration.InstanceValue.maxSatisfied (render G vertices edges tables hM) =
      G.maxSatisfied := by
  classical
  apply Nat.le_antisymm
  · unfold Integration.InstanceValue.maxSatisfied
    apply Finset.sup_le
    intro labeling _
    erw [render_count G vertices edges tables hM htable]
    exact G.satisfiedCount_le_maxSatisfied _ _
  · unfold BipartiteGame.maxSatisfied
    apply Finset.sup_le
    intro labeling _
    rw [← render_count_merge G vertices edges tables hM htable]
    exact Integration.InstanceValue.countSatisfied_le_maxSatisfied
      (render G vertices edges tables hM) (mergeLabelings vertices labeling.1 labeling.2)

theorem render_value (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (htable : ∀ e, permutationEquiv (tables e) = G.permutation e) :
    Integration.InstanceValue.value (render G vertices edges tables hM) = G.value := by
  unfold Integration.InstanceValue.value BipartiteGame.value
  rw [render_maxSatisfied G vertices edges tables hM htable, render_length]
  have hcard : M = Fintype.card E := by simpa using Fintype.card_congr edges
  rw [hcard]

end Value

end MaxCutGames.Explicit.ProductTarget

/-!
Concrete numbered, full-table output for the v2 four-edge subdivision.
Original vertices keep their names. The new names are `n+e`, `n+Q+2e`,
and `n+Q+2e+1`, and each input occurrence emits four consecutive rows.
-/

namespace MaxCutGames.Explicit.SubdivisionTarget

open MaxCutGames.Foundations Target
open MachineOutputContract
open scoped BigOperators

theorem ofInstance_count {q : Nat} (H : Instance q) (a : Fin H.vertices → Fin q) :
    (ofInstance H).satisfiedCount a = countSatisfied a H.constraints := by
  have h := Integration.GapSemantics.countSatisfied_ofFn a
    (fun i : Fin H.constraints.length => H.constraints[i.val])
  rw [List.ofFn_getElem] at h
  rw [h]
  simp only [OccurrenceGame.satisfiedCount, ofInstance, permutationEquiv,
    Equiv.coe_fn_mk, Constraint.satisfied, decide_eq_true_eq, Fin.getElem_fin]
  rfl

theorem ofInstance_maxSatisfied {q : Nat} (H : Instance q) :
    (ofInstance H).maxSatisfied = Integration.InstanceValue.maxSatisfied H := by
  classical
  unfold OccurrenceGame.maxSatisfied Integration.InstanceValue.maxSatisfied
  apply Finset.sup_congr
  · ext a
    simp only [Finset.mem_univ]
  · intro a _
    exact ofInstance_count H a

theorem ofInstance_value {q : Nat} (H : Instance q) :
    (ofInstance H).value = Integration.InstanceValue.value H := by
  unfold OccurrenceGame.value Integration.InstanceValue.value
  rw [ofInstance_maxSatisfied]
  simp

theorem tables_correspond {q : Nat} (H : Instance q)
    (ei : Fin H.constraints.length × Fin 4) :
    permutationEquiv (tables H ei) = (Subdivision.game (ofInstance H)).permutation ei := by
  ext a
  by_cases hi : ei.2 = 3 <;>
    simp [tables, permutationEquiv, Subdivision.game, Subdivision.permutation, ofInstance,
      MachineSubdivisionRows.inverseTable, MachineSubdivisionRows.identityTable, hi]

theorem tables_translation {q s : Nat}
    (coordinates : Fin q ≃ Integration.BinaryLinear.Vector s) (H : Instance q)
    (hH : Integration.TranslationTarget.IsTranslationInstance coordinates H)
    (ei : Fin H.constraints.length × Fin 4) :
    ∃ shift : Integration.BinaryLinear.Vector s, ∀ a : Fin q,
      coordinates ((tables H ei).images[a]) = coordinates a + shift := by
  by_cases hi : ei.2 = 3
  · obtain ⟨shift, hs⟩ := hH H.constraints[ei.1] (List.getElem_mem ei.1.isLt)
    refine ⟨shift, ?_⟩
    intro a
    simp only [tables, hi, ite_eq_left, MachineSubdivisionRows.inverseTable]
    have h := hs (H.constraints[ei.1].permutation.inverseImages[a])
    rw [H.constraints[ei.1].permutation.rightInverse] at h
    have hc := congrArg (fun x => x + shift) h
    simpa only [add_assoc, ZModModule.add_self, add_zero] using hc.symm
  · refine ⟨0, ?_⟩
    intro a
    simp [tables, hi, MachineSubdivisionRows.identityTable]

theorem subdivide_translation {q s : Nat}
    (coordinates : Fin q ≃ Integration.BinaryLinear.Vector s) (H : Instance q)
    (hH : Integration.TranslationTarget.IsTranslationInstance coordinates H) :
    Integration.TranslationTarget.IsTranslationInstance coordinates (subdivide H) := by
  intro c hc
  change c ∈ List.ofFn _ at hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  exact tables_translation coordinates H hH (numericEdgeEquiv H.constraints.length i)

def simpleBipartite {q : Nat} (H : Instance q) : SimpleBipartite (subdivide H) :=
  ProductTarget.render_simpleBipartite _ _ _ _ _

/-- The serialized output has exactly the abstract subdivision value. -/
theorem subdivide_value {q : Nat} (H : Instance q) :
    Integration.InstanceValue.value (subdivide H) =
      (Subdivision.game (ofInstance H)).value :=
  ProductTarget.render_value _ _ _ _ _ (tables_correspond H)

/-- Exact equation (bipartization-value) for the concrete list/table format. -/
theorem value_eq {q : Nat} (H : Instance q) (hq : 0 < q) :
    Integration.InstanceValue.value (subdivide H) =
      1 - (1 - Integration.InstanceValue.value H) / 4 := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  let : Nonempty (Fin H.constraints.length) := ⟨⟨0, H.constraintCount_positive⟩⟩
  rw [subdivide_value, Subdivision.value_eq, ofInstance_value]

end MaxCutGames.Explicit.SubdivisionTarget

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Product
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The independent graph product in the last step of the v2 reduction.

Edges are tuples of actual base edges.  The endpoint maps remain injective,
the edge law is exactly uniform, and the associated game agrees with ordinary
parallel repetition for every pair of local strategies, including strategies
depending on their whole question tuples.  Only the completeness lower bound
uses coordinatewise strategies; no repetition soundness bound is assumed here.
-/

/-!
Machine-friendly product numbering on the common global vertex base.
Both endpoints use the same radix, so the machine needs neither a right-side
subtraction nor a final offset. Mixed-side tuples are isolated vertices. For a
positive repetition count the first coordinate supplies a total bipartition.
-/

namespace MaxCutGames.Explicit.ProductPaddedOutput

open MaxCutGames.Foundations
open Target
open MachineOutputContract
open ProductTarget
open scoped BigOperators

variable {q : ℕ} (H : Instance q) (presentation : SimpleBipartite H)

def finalCoordinates {ell : ℕ} (coordinates : Fin q ≃ (Fin ell → ZMod 2)) (t : ℕ) :
    Fin (q ^ t) ≃ (Fin (ell * t) → ZMod 2) :=
  finFunctionFinEquiv.symm.trans
    ((Equiv.piCongrRight (fun _ : Fin t => coordinates)).trans
      (BipartiteGame.binaryProductEquiv ell t).toEquiv)

theorem finalCoordinates_apply {ell : ℕ}
    (coordinates : Fin q ≃ (Fin ell → ZMod 2)) (t : ℕ) (a : Fin (q ^ t)) :
    finalCoordinates coordinates t a = BipartiteGame.binaryProductEquiv ell t
      (fun i => coordinates (finFunctionFinEquiv.symm a i)) := rfl

local instance instNonemptyFinLengthConstraintVerticesConstraints_re18046_1 : Nonempty (Fin H.constraints.length) := ⟨⟨0, H.constraintCount_positive⟩⟩
theorem output_translations {ell : ℕ}
    (coordinates : Fin q ≃ (Fin ell → ZMod 2))
    (hH : Integration.TranslationTarget.IsTranslationInstance coordinates H)
    (t : ℕ) (ht : 0 < t) :
    Integration.TranslationTarget.IsTranslationInstance (finalCoordinates coordinates t)
      (output H presentation t ht) := by
  classical
  choose offset hoffset using fun e : Fin H.constraints.length =>
    hH H.constraints[e] (List.getElem_mem e.isLt)
  intro constraint hconstraint
  rw [output_constraints] at hconstraint
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hconstraint
  refine ⟨BipartiteGame.binaryProductEquiv ell t
    (fun j => offset (finFunctionFinEquiv.symm i j)), ?_⟩
  intro a
  rw [outputRow_images]
  simp only [finalCoordinates_apply, Equiv.symm_apply_apply]
  rw [← map_add]
  congr 1
  funext j
  exact hoffset _ _

end MaxCutGames.Explicit.ProductPaddedOutput

end OAI
end


