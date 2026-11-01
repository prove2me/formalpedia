-- Prove2me | Definitions.Def_OAIQ053K047
-- name    : OAIQ053K047
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:05:45.650729+00:00
-- url     : https://prove2.me/theorems/4d172b7c-3365-4f4f-ad60-032ade36ab00
-- title:
--   Definitions bundle OAIQ053K047 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 49 declarations of OpenAI's Lean: 36 definitions, 1 inductive type or structure, 2 instances and 10 theorems. The definitions and types are `OAI.MetricKMedian.LPBinary.Program.rawContextProgram`, `OAI.MetricKMedian.LPBinary.Program.rawGradProgram`, `OAI.MetricKMedian.LPBinary.Program.rawInitialProgram`, `OAI.MetricKMedian.LPBinary.Program.rawPenaltyProgram`, `OAI.MetricKMedian.LPBinary.Program.rawRateProgram`, `OAI.MetricKMedian.LPBinary.Program.rawStepsProgram`, `OAI.MetricKMedian.LPBinary.Program.truncateMatrixProgram`, `OAI.MetricKMedian.LPBinary.Program.truncateRowProgram`, `OAI.MetricKMedian.LPBinary.Program.upperProgram`, `OAI.MetricKMedian.LPBinary.Repair.boundedProgram`, `OAI.MetricKMedian.LPBinary.Repair.lossProgram`, `OAI.MetricKMedian.LPBinary.Repair.openingProgram`, `OAI.MetricKMedian.LPBinary.Repair.weightsProgram`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.RightSize`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.badNodes`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.neutralTable`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.rightOrder`, `OAI.MetricKMedian.PCP.FlexibleAmplifier.bits`, `OAI.MetricKMedian.PCP.FlexibleAmplifier.powered`, `OAI.MetricKMedian.PCP.FlexibleRegularization.decoded`, `OAI.MetricKMedian.PCP.InitialAlphabet.bits`, `OAI.MetricKMedian.PCP.ProjectionSeed.Degree`, `OAI.MetricKMedian.PCP.ProjectionSeed.LeftPort`, `OAI.MetricKMedian.PCP.ProjectionSeed.Port`, `OAI.MetricKMedian.PCP.ProjectionSeed.RightLabel`, `OAI.MetricKMedian.PCP.ProjectionSeed.contraction`, `OAI.MetricKMedian.PCP.ProjectionSeed.gap`, `OAI.MetricKMedian.Preparation.RationalUnitInput.ScanProgram.Input.sup`, `OAI.MetricKMedian.Reduction.Program.Branch`, `OAI.MetricKMedian.Reduction.Program.Branch.allowed`, `OAI.MetricKMedian.Reduction.Program.Branch.restricted`, `OAI.MetricKMedian.Reduction.Program.feasible`, `OAI.MetricKMedian.Reduction.Program.selectList`, `OAI.MetricKMedian.RoundingProgram.WeightedRound.result`, `OAI.MetricKMedian.SparseBundles.Program.QInput.input`, `OAI.MetricKMedian.SparseEnumeratedBernoulli.law`, `OAI.MetricKMedian.SparseStarActivation.Program.Input.graph`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Amplification_FlexibleAmplifier`, `KMedian_Amplification_FlexibleRegularization`, `KMedian_Amplification_RegularGraphLaws`, `KMedian_CookLevin_InitialAlphabet`, `KMedian_CookLevin_SeedInput`, `KMedian_Expanders_CloudOrder`, `KMedian_Machines_MatchingLaws`, `KMedian_Optimization_ApproximationListProgram`, `KMedian_Optimization_FractionalListChecks`, `KMedian_Optimization_LPBinaryStart`, `KMedian_Optimization_SimplexListProgram`, `KMedian_Optimization_TruncatedListCompiler`, `KMedian_PCP_GlobalRegularization`, `KMedian_Programs_BranchProgram`, `KMedian_Programs_BundlesProgram`, `KMedian_Programs_FinalSelectionProgram`, `KMedian_Programs_LastFractionProgram`, `KMedian_Programs_StarActivationProgram`, `KMedian_Programs_UnitScanProgram`, `KMedian_Projection_Seed`, `KMedian_Projection_SeedTables`, `KMedian_Sparse_SparseEnumeratedCount`.
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundles `OAIQ053K026`, `OAIQ053K038`, `OAIQ053K039`, `OAIQ053K040`, `OAIQ053K041` and `OAIQ053K042` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K051`, `OAIQ053K052` and `OAIQ053K053`; the statements `OAI.MetricKMedian.PCP.FlexibleAmplifier.sound_of_power_bound_s53`, `OAI.MetricKMedian.SparseEnumeratedBatch.prob_eq_s53` and `OAI.MetricKMedian.SparseFixedCount.actual_count_tail_s53`; the proofs of `OAI.MetricKMedian.PCP.FlexibleAmplifier.sound_of_power_bound_s53`, `OAI.MetricKMedian.SparseCopyState.physical_count_tail_s53`, `OAI.MetricKMedian.SparseEnumeratedBatch.prob_eq_s53` and `OAI.MetricKMedian.SparseFixedCount.actual_count_tail_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K026
import Definitions.Def_OAIQ053K038
import Definitions.Def_OAIQ053K039
import Definitions.Def_OAIQ053K040
import Definitions.Def_OAIQ053K041
import Definitions.Def_OAIQ053K042

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_GlobalRegularization
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPGlobalRegularization

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace GlobalRegularization
variable {V E A : Type} [Fintype E] [Nonempty E]
  [Fintype A] [DecidableEq A] [Inhabited A]
variable (C : BinaryCSP V E A)

omit [Fintype A] [DecidableEq A] [Inhabited A] in
lemma node_relative_upper : Fintype.card (Node C) ≤
    ExpanderFamily.growth*Fintype.card (CloudCopies.Node C) := by
  have h := ExpanderFamily.padding_upper (Fintype.card (CloudCopies.Node C)-1)
  have hp := Fintype.card_pos (α := CloudCopies.Node C)
  simp only [← Nat.card_eq_fintype_card] at hp
  simpa only [Node,depth,← Nat.card_eq_fintype_card,Nat.sub_add_cancel hp] using h

omit [Fintype A] [DecidableEq A] [Inhabited A] in
lemma node_upper : Fintype.card (Node C) ≤ 2*ExpanderFamily.growth^2*Fintype.card E := by
  calc
    _ ≤ ExpanderFamily.growth*Fintype.card (CloudCopies.Node C) := node_relative_upper C
    _ ≤ ExpanderFamily.growth*(2*ExpanderFamily.growth*Fintype.card E) :=
      Nat.mul_le_mul_left _ (CloudCopies.node_card_upper C)
    _ = _ := by ring

end GlobalRegularization
end MetricKMedian.PCP

end Inline_PCPGlobalRegularization

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_FlexibleRegularization
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFlexibleRegularization

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace FlexibleRegularization
variable {V E A : Type} [Fintype V] [Fintype E] [Nonempty E]
  [Fintype A] [DecidableEq A] [Inhabited A]
variable (C : BinaryCSP V E A)

open GlobalRegularization

variable (cloudEmbed : ∀ v : CloudCopies.Active C, CloudCopies.Incident C v ↪ CloudCopies.Copy C v)
variable (padEmbed : CloudCopies.Node C ↪ Node C)

noncomputable def decoded (a : Node C → A) : V → A :=
  CloudCopies.decoded C (a ∘ padEmbed)

end FlexibleRegularization
end MetricKMedian.PCP

end Inline_PCPFlexibleRegularization

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_FlexibleAmplifier
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFlexibleAmplifier

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace FlexibleAmplifier
open Amplifier

variable {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
variable (C : BinaryCSP V E Label)
variable (cloudEmbed : ∀ v : CloudCopies.Active C, CloudCopies.Incident C v ↪ CloudCopies.Copy C v)
variable (padEmbed : CloudCopies.Node C ↪ GlobalRegularization.Node C)
noncomputable instance edgeFintype : Fintype (Edge C cloudEmbed padEmbed) := inferInstance
noncomputable def powered : BinaryCSP (Node C) (Edge C cloudEmbed padEmbed) (Advice Degree Label radius) := (FlexibleRegularization.csp C cloudEmbed padEmbed).powered (cap := radius) steps
noncomputable def bits : BinaryCSP (Node C) (Edge C cloudEmbed padEmbed) (BitVector Bits) :=
  (powered C cloudEmbed padEmbed).mapLabels (Advice.bitsEquiv Degree (Fin 4) radius)

end FlexibleAmplifier
end MetricKMedian.PCP

end Inline_PCPFlexibleAmplifier

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_RegularGraphLaws
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRegularGraphLaws
namespace MetricKMedian.PCP.FlexibleRegularization
open scoped Classical

variable {V E A : Type} [Fintype V] [Fintype E] [Nonempty E] [Fintype A] [DecidableEq A] [Inhabited A]
variable (C : BinaryCSP V E A)
variable (cloudEmbed : ∀ v : CloudCopies.Active C, CloudCopies.Incident C v ↪ CloudCopies.Copy C v)
variable (padEmbed : CloudCopies.Node C ↪ GlobalRegularization.Node C)
omit [Fintype V] [Nonempty E] [Fintype A] [DecidableEq A] [Inhabited A] in
lemma graph_coded (code : GlobalRegularization.Node C → ℕ) (v : GlobalRegularization.Node C)
    (d : GlobalRegularization.Degree) :
    (code ((graph C cloudEmbed padEmbed).step v d),(graph C cloudEmbed padEmbed).back v d)=
      if d.1=0 then (code ((padGraph C cloudEmbed padEmbed).step v d.2.1),
        (d.1,((padGraph C cloudEmbed padEmbed).back v d.2.1,d.2.2)))
      else (code ((GlobalRegularization.strong C).step v d.2.2),
        (d.1,(d.2.1,(GlobalRegularization.strong C).back v d.2.2))) :=
  PortGraph.blend_coded _ _ code v d
omit [Fintype V] [Nonempty E] [Fintype A] [DecidableEq A] [Inhabited A] in
lemma padded_rotate_image (p : CloudCopies.Node C) (d : CloudCopies.RegularPort) :
    (padGraph C cloudEmbed padEmbed).rotate (padEmbed p,d)=
      (padEmbed ((FlexibleCloud.regularGraph C cloudEmbed).step p d),
        (FlexibleCloud.regularGraph C cloudEmbed).back p d) := by
  exact (FlexibleCloud.regularGraph C cloudEmbed).extend_rotate_image padEmbed (p,d)
omit [Fintype V] [Nonempty E] [Fintype A] [DecidableEq A] [Inhabited A] in
lemma padded_rotate_outside (v : GlobalRegularization.Node C) (d : CloudCopies.RegularPort)
    (hv : v∉Set.range padEmbed) :
    (padGraph C cloudEmbed padEmbed).rotate (v,d)=(v,d) := by
  exact (FlexibleCloud.regularGraph C cloudEmbed).extend_rotate_outside padEmbed (v,d) hv
omit [Fintype V] [Nonempty E] [Inhabited A] in
lemma padded_allowed_image (p : CloudCopies.Node C) (d : CloudCopies.RegularPort) :
    (padded C cloudEmbed padEmbed).allowed (padEmbed p,d)=
      (FlexibleCloud.regularCSP C cloudEmbed).allowed (p,d) := by
  exact (FlexibleCloud.regularCSP C cloudEmbed).extendedAllowed_image padEmbed (p,d)
omit [Fintype V] [Nonempty E] [Inhabited A] in
lemma padded_allowed_outside (v : GlobalRegularization.Node C) (d : CloudCopies.RegularPort)
    (hv : v∉Set.range padEmbed) :
    (padded C cloudEmbed padEmbed).allowed (v,d)=Finset.univ := by
  exact (FlexibleCloud.regularCSP C cloudEmbed).extendedAllowed_outside padEmbed (v,d) hv
end MetricKMedian.PCP.FlexibleRegularization

end Inline_PCPRegularGraphLaws

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_InitialAlphabet
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInitialAlphabet

namespace MetricKMedian.PCP
open Function Finset
open scoped Classical

namespace InitialAlphabet
variable (A : Type) [Fintype A] [DecidableEq A] [Nonempty A]
variable {V E : Type} [Fintype V] [Fintype E]
variable (C : BinaryCSP V E A)
noncomputable def bits : BinaryCSP V E (BitVector A) := C.pullLabels (decode A)
end InitialAlphabet
end MetricKMedian.PCP

end Inline_PCPInitialAlphabet

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_CloudOrder
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCloudOrder
namespace MetricKMedian.PCP.Compiler.CloudOrder
open scoped Classical

variable {V E A : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
variable (C : BinaryCSP V E A) (vo : Ordered V) (eo : Ordered E)
omit [DecidableEq E] in
lemma nodeCode_injective : Function.Injective (nodeCode C vo) := by
  apply sigmaCode_injective (fun v : CloudCopies.Active C => (vo.equiv v.val).val)
    (fun v w => (ExpanderFamily.vertexEquiv (CloudCopies.depth C v) w).val)
  · exact Fin.val_injective.comp (vo.equiv.injective.comp Subtype.val_injective)
  · intro v
    exact Fin.val_injective.comp (ExpanderFamily.vertexEquiv (CloudCopies.depth C v)).injective
end MetricKMedian.PCP.Compiler.CloudOrder

end Inline_PCPCloudOrder

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_MatchingLaws
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPMatchingLaws
namespace MetricKMedian.PCP.FlexibleCloud
open scoped Classical

variable {V E A : Type} [Fintype E] (C : BinaryCSP V E A)
variable (embed : ∀ v : CloudCopies.Active C, CloudCopies.Incident C v ↪ CloudCopies.Copy C v)
lemma matching_step_image (d : CloudCopies.Dart (E := E)) :
    (matchingGraph C embed).step (dartEmbed C embed d) ()=dartEmbed C embed (CloudCopies.dartFlip d) := by
  unfold matchingGraph
  rw [PortGraph.extend_step_image]
  rfl
lemma matching_step_outside (p : CloudCopies.Node C) (hp : p∉Set.range (dartEmbed C embed)) :
    (matchingGraph C embed).step p ()=p := by
  exact congrArg Prod.fst ((CloudCopies.dartGraph (E := E)).extend_rotate_outside (dartEmbed C embed) (p,()) hp)
end MetricKMedian.PCP.FlexibleCloud

end Inline_PCPMatchingLaws

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_Seed
attribute [-instance] _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionSeed

namespace MetricKMedian.PCP
open Finset
open scoped Classical BigOperators

namespace ProjectionSeed
open Amplifier

noncomputable def gap : ℝ := 1/(capLoss:ℝ)/(18*(ExpanderFamily.growth:ℝ)^2)
noncomputable def contraction : ℝ := max (1-(1/4:ℝ)*((gap/2)/4)^2) (1-(1:ℝ)/1024)

abbrev Degree := GlobalRegularization.Degree
abbrev Port := (Degree × Bool) × Bool
abbrev RightLabel := Label × Bool
abbrev LeftPort := Bool × Bool
end ProjectionSeed
end MetricKMedian.PCP

end Inline_PCPProjectionSeed

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_SeedTables
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSeedTables
namespace MetricKMedian.PCP.Compiler.SeedProgram
open Binary Binary.Automatic Amplifier ProjectionTable
open scoped Classical

noncomputable def neutralTable : ProjectionTable Bool Bool :=
  build (BiProjection.neutral Bool Bool Bool Bool) (Fintype.equivFin Bool) (Ordered.fixed Bool) (Ordered.fixed Bool)
noncomputable def badNodes := (Ordered.fixed Bool).prod (Ordered.fixed Bool)
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPSeedTables

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_SeedInput
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSeedInput
namespace MetricKMedian.PCP.Compiler.SeedProgram
open Binary Binary.Automatic Amplifier ProjectionTable
open scoped Classical

noncomputable def rightOrder := Ordered.fixed ProjectionSeed.RightLabel
noncomputable abbrev RightSize (n : ℕ) := (rightOrder.nested n).entries.length
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPSeedInput

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_SimplexListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Finset

namespace Program
open Binary Binary.PolyProgram
noncomputable def upperProgram : PolyProgram (encodePair Ratio.encode er) er (fun x : ℚ × Row => upper x.2 x.1) :=
  (listFilterWith ratLE 0 0).congr _ (fun _ => rfl)
end Program
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_TruncatedListCompiler
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.LPBinary.Program
open Binary Binary.PolyProgram Function

noncomputable def truncateRowProgram : PolyProgram (encodePair Ratio.encode er) er (fun x : ℚ × Row => Truncated.row x.2 x.1) := by
  let t := snd Ratio.encode Ratio.encode
  let test := (t.fanout (constant (encodePair Ratio.encode Ratio.encode) Ratio.encode 1)).comp ratLE
  let coord := ite test (fst Ratio.encode Ratio.encode) t
  exact (coord.listMapWith 0 0).congr _ (fun x => by simp only [Function.comp_apply,decide_eq_true_eq,Truncated.row])

noncomputable def truncateMatrixProgram : PolyProgram (encodePair ers Ratio.encode) ers (fun x : Rows × ℚ => Truncated.matrix x.1 x.2) :=
  ((exchange ers Ratio.encode).comp (truncateRowProgram.listMapWith [] [])).congr _ (fun _ => rfl)

end MetricKMedian.LPBinary.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_LPBinaryStart
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function

namespace Program
noncomputable def rawPenaltyProgram (r : ℕ) : PolyProgram ei Nat.bits (rawPenalty r) := by
  let k := snd ers Nat.bits
  let p := (k.fanout (constant ei Nat.bits 1)).comp natAdd
  exact ((constant ei Nat.bits (4*r)).fanout p |>.comp natMul).congr _ (fun _ => rfl)
noncomputable def rawGradProgram (r : ℕ) : PolyProgram ei Nat.bits (rawGrad r) := by
  let ds := fst ers Nat.bits
  let n := (ds.comp (listHead er [])).comp (listLength Ratio.encode 0)
  let m := ds.comp (listLength er [])
  let mh := (m.fanout (rawPenaltyProgram r)).comp natMul
  exact ((n.fanout ((mh.fanout mh).comp natMul)).comp natMul).congr _ (fun x => by dsimp only [Function.comp_apply,rawGrad]; rw [pow_two])
noncomputable def rawRateProgram (r : ℕ) : PolyProgram ei Ratio.encode (rawRate r) := by
  let grad := (rawGradProgram r).comp ratOfNat
  let den := ((constant ei Ratio.encode (2*(r:ℚ))).fanout grad).comp ratMul
  exact (den.comp ratInv).congr _ (fun x => by simp only [Function.comp_apply,rawRate,one_div])
noncomputable def rawStepsProgram (r : ℕ) : PolyProgram ei Nat.bits (rawSteps r) := by
  let k := snd ers Nat.bits
  let kk := (k.fanout k).comp natMul
  let g := ((constant ei Nat.bits (8*r^2)).fanout (rawGradProgram r)).comp natMul
  exact ((g.fanout kk).comp natMul).congr _ (fun _ => by dsimp only [Function.comp_apply,rawSteps]; simp only [pow_two])
noncomputable def rawContextProgram (r : ℕ) : PolyProgram ei ec (rawContext r) :=
  ((fst ers Nat.bits).fanout (((rawPenaltyProgram r).comp ratOfNat).fanout (((snd ers Nat.bits).comp ratOfNat).fanout (rawRateProgram r)))).congr _ (fun _ => rfl)
noncomputable def rawInitialProgram : PolyProgram ei er rawInitial := by
  let ids := ((fst ers Nat.bits).comp (listHead er [])).comp (listIndices Ratio.encode 0)
  let k := (snd ers Nat.bits).comp ratOfNat
  let test := (snd Ratio.encode Nat.bits).comp natZero
  let coord := ite test (constant (encodePair Ratio.encode Nat.bits) Ratio.encode 0) (fst Ratio.encode Nat.bits)
  exact ((k.fanout ids).comp (coord.listMapWith 0 0)).congr _ (fun x => by simp only [Function.comp_apply,rawInitial,decide_eq_true_eq])
end Program

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_ApproximationListProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Repair

noncomputable def openingProgram : PolyProgram (encodePair er Ratio.encode) er (fun x : Row × ℚ => opening x.1 x.2) := by
  let y := snd Ratio.encode Ratio.encode
  let den := ((constant (encodePair Ratio.encode Ratio.encode) Ratio.encode 1).fanout (fst Ratio.encode Ratio.encode)).comp ratSub
  let val := (y.fanout den).comp ratDiv
  let coord := ((constant (encodePair Ratio.encode Ratio.encode) Ratio.encode 1).fanout val).comp Program.ratMin
  exact ((exchange er Ratio.encode).comp (coord.listMapWith 0 0)).congr _ (fun _ => rfl)
noncomputable def weightsProgram : PolyProgram (encodePair er er) er (fun x : Row × Row => weights x.1 x.2) := by
  let test := ((fst Ratio.encode Ratio.encode).fanout (constant (encodePair Ratio.encode Ratio.encode) Ratio.encode 1)).comp ratLE
  let coord := ite test (constant (encodePair Ratio.encode Ratio.encode) Ratio.encode 0) (snd Ratio.encode Ratio.encode)
  exact ((listZip Ratio.encode Ratio.encode 0 0).comp (coord.listMap (0,0))).congr _ (fun _ => by simp only [Function.comp_apply,weights,decide_eq_true_eq])
noncomputable def lossProgram (r : ℕ) : PolyProgram ei Ratio.encode (fun x : Rows × ℕ => TruncatedLP.loss r x.2) :=
  (((constant ei Ratio.encode (1+1/(r:ℚ))).fanout ((Program.rawPenaltyProgram r).comp ratOfNat)).comp ratDiv).congr _ (fun _ => rfl)
end Repair
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_FractionalListChecks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.LPBinary.Repair
open Binary Binary.PolyProgram Function Finset

noncomputable def boundedProgram : PolyProgram Ratio.encode encodeBool bounded := by
  let lo := ((constant Ratio.encode Ratio.encode 0).fanout (identity Ratio.encode)).comp ratLE
  let hi := ((identity Ratio.encode).fanout (constant Ratio.encode Ratio.encode 1)).comp ratLE
  exact ((lo.fanout hi).comp boolAnd).congr _ (fun q => by simp only [Function.comp_apply,id_eq,bounded,Bool.decide_and])
end MetricKMedian.LPBinary.Repair
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseEnumeratedCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedBernoulli
open Finset
variable {E : Type} [Fintype E] [DecidableEq E] {n : ℕ}

def law (enum : Fin n ≃ E) (q : E → ℚ) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) :
    SparseIntegerLaw (E → Bool) :=
  (SparseBernoulli.run (d := 4) (fun a => q (enum a)) (fun a => hq (enum a)) n).map
    (fun ω e => ω (enum.symm e))

end MetricKMedian.SparseEnumeratedBernoulli
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_LastFractionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MetricKMedian.RoundingProgram.WeightedRound
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse

def result (x : Input false) : RoundingProgram.State false :=
  ⟨x.n,x.β,x.positive,SparseWeightedRounding.round x.β (x.positive rfl) x.p⟩
end MetricKMedian.RoundingProgram.WeightedRound
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_StarActivationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.SparseStarActivation.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView indices)
def Input.graph (x : Input) : SparseGraph.Program.Input :=
  ⟨x.n,x.m,fun e => SparseTargetSubset.law (x.D e) (x.q e)⟩
end MetricKMedian.SparseStarActivation.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_BundlesProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseBundles.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open SparseIntegerLaw.DependentProgram SparseCounts.Program
def QInput.input (x : QInput) : Input := ⟨x.n,x.m,(fun j => SparseGridRounding.law (fun i => x.q i j))⟩
end MetricKMedian.SparseBundles.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_UnitScanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Preparation.RationalUnitInput.ScanProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open Program
variable {η τ : ℝ} (p : RationalAllParameters η τ)
def Input.sup (x : Input) : RationalSuppliers.Program.ScanInput :=
  letI := x.metric
  ⟨x.f,(x.U.representatives p.M).card,x.j,x.U.suppliers x.R p,x.U.df,x.U.dc,x.B⟩
end MetricKMedian.Preparation.RationalUnitInput.ScanProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_BranchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Reduction.Program
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open Enumeration
structure Branch where
  original : Instance
  facilities : Finset (Fin original.n)
namespace Branch
def allowed (B : Branch) : Prop := B.original.k ≤ B.facilities.card
instance instDecidablePredAllowed : DecidablePred allowed := fun B => inferInstanceAs (Decidable (B.original.k≤B.facilities.card))
def restricted (B : Branch) (h : B.allowed) : Instance := B.original.restrictFacilities B.facilities h
end Branch
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_FinalSelectionProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Reduction.Program
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
def feasible (I : Instance) (S : Finset (Fin I.n)) : Bool := decide (S⊆I.facilities ∧ S.Nonempty ∧ S.card≤I.k)
def selectList (I : Instance) (L : List (Finset (Fin I.n))) : Finset (Fin I.n) :=
  (SparseSelect.best (feasible I) (rationalCost I) L).getD {I.facilities.min' I.facilities_nonempty}
end MetricKMedian.Reduction.Program
end

end OAI
end


