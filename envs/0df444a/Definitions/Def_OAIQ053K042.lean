-- Prove2me | Definitions.Def_OAIQ053K042
-- name    : OAIQ053K042
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:03:50.849586+00:00
-- url     : https://prove2.me/theorems/862280df-f4ea-4197-b808-6484be954fbb
-- title:
--   Definitions bundle OAIQ053K042 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 77 declarations of OpenAI's Lean: 49 definitions, 5 instances, 21 theorems and 2 other declarations. The definitions and types are `OAI.MetricKMedian.LPBinary.Program.candidatesProgram`, `OAI.MetricKMedian.PCP.Amplifier.Bits`, `OAI.MetricKMedian.PCP.Amplifier.Degree`, `OAI.MetricKMedian.PCP.Amplifier.Node`, `OAI.MetricKMedian.PCP.Amplifier.WalkData`, `OAI.MetricKMedian.PCP.Amplifier.walkCoeff`, `OAI.MetricKMedian.PCP.CloudCopies.Disagrees`, `OAI.MetricKMedian.PCP.CloudCopies.RegularPort`, `OAI.MetricKMedian.PCP.CloudCopies.dartCSP`, `OAI.MetricKMedian.PCP.CloudCopies.dartGraph`, `OAI.MetricKMedian.PCP.CloudCopies.equalityCSP`, `OAI.MetricKMedian.PCP.CloudCopies.honest`, `OAI.MetricKMedian.PCP.Compiler.CloudOrder.activeOrder`, `OAI.MetricKMedian.PCP.Compiler.CloudOrder.cloudEmbed`, `OAI.MetricKMedian.PCP.Compiler.CloudOrder.copyOrder`, `OAI.MetricKMedian.PCP.Compiler.CloudOrder.dartOrder`, `OAI.MetricKMedian.PCP.Compiler.CloudOrder.incidentOrder`, `OAI.MetricKMedian.PCP.Compiler.CloudOrder.nodeCode`, `OAI.MetricKMedian.PCP.Compiler.CloudOrder.nodeOrder`, `OAI.MetricKMedian.PCP.Compiler.CloudOrder.padEmbed`, `OAI.MetricKMedian.PCP.Compiler.RegularProgram.Port`, `OAI.MetricKMedian.PCP.Compiler.RegularProgram.RPort`, `OAI.MetricKMedian.PCP.FlexibleAmplifier.Edge`, `OAI.MetricKMedian.PCP.FlexibleAmplifier.Node`, `OAI.MetricKMedian.PCP.FlexibleCloud.RegularPort`, `OAI.MetricKMedian.PCP.FlexibleCloud.dartEmbed`, `OAI.MetricKMedian.PCP.FlexibleCloud.matchingCSP`, `OAI.MetricKMedian.PCP.FlexibleCloud.matchingGraph`, `OAI.MetricKMedian.PCP.FlexibleCloud.regularCSP`, `OAI.MetricKMedian.PCP.FlexibleCloud.regularGraph`, `OAI.MetricKMedian.PCP.FlexibleRegularization.csp`, `OAI.MetricKMedian.PCP.FlexibleRegularization.graph`, `OAI.MetricKMedian.PCP.FlexibleRegularization.padGraph`, `OAI.MetricKMedian.PCP.FlexibleRegularization.padded`, `OAI.MetricKMedian.PCP.GlobalRegularization.Degree`, `OAI.MetricKMedian.PCP.GlobalRegularization.FastPort`, `OAI.MetricKMedian.PCP.GlobalRegularization.Node`, `OAI.MetricKMedian.PCP.GlobalRegularization.StrongPort`, `OAI.MetricKMedian.PCP.GlobalRegularization.depth`, `OAI.MetricKMedian.PCP.GlobalRegularization.strong` and 9 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Amplification_Amplifier`, `KMedian_Amplification_AmplifierSize`, `KMedian_Amplification_CSPMix`, `KMedian_Amplification_FlexibleAmplifier`, `KMedian_Amplification_FlexibleCloud`, `KMedian_Amplification_FlexibleRegularization`, `KMedian_Amplification_RegularGraphLaws`, `KMedian_Amplification_RegularPrograms`, `KMedian_Amplification_RegularizationObjects`, `KMedian_Amplification_RegularizationSound`, `KMedian_Expanders_CloudOrder`, `KMedian_Expanders_CloudSpec`, `KMedian_Expanders_GraphExtend`, `KMedian_Geometry_NearestFillingFormula`, `KMedian_Machines_IterationPolynomial`, `KMedian_Machines_MatchingLaws`, `KMedian_Optimization_DualListCompiler`, `KMedian_Optimization_FractionalInputProgram`, `KMedian_Optimization_IntegralFractionalComparison`, `KMedian_PCP_GlobalRegularization`, `KMedian_Process_CountRunProgram`, `KMedian_Process_CountStepProgram`, `KMedian_Programs_LastFractionProgram`, `KMedian_Programs_NearestListProgram`, `KMedian_Programs_UnitScanProgram`, `KMedian_Rounding_SignedTerminalProgram`, `KMedian_Sparse_SparseProduct`.
--
--   **Imports.** It imports the bundles `OAIQ053K028`, `OAIQ053K029`, `OAIQ053K030`, `OAIQ053K031`, `OAIQ053K032`, `OAIQ053K033`, `OAIQ053K034` and `OAIQ053K035` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K046` and `OAIQ053K047`; the statements `OAI.MetricKMedian.PCP.FlexibleCloud.regular_sound_s53`, `OAI.MetricKMedian.PCP.FlexibleRegularization.contracts_s53` and `OAI.MetricKMedian.PCP.GlobalRegularization.strong_contracts_s53`; the proofs of `OAI.MetricKMedian.PCP.FlexibleCloud.regular_sound_s53`, `OAI.MetricKMedian.PCP.FlexibleRegularization.contracts_s53` and `OAI.MetricKMedian.PCP.GlobalRegularization.strong_contracts_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K028
import Definitions.Def_OAIQ053K029
import Definitions.Def_OAIQ053K030
import Definitions.Def_OAIQ053K031
import Definitions.Def_OAIQ053K032
import Definitions.Def_OAIQ053K033
import Definitions.Def_OAIQ053K034
import Definitions.Def_OAIQ053K035

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_GraphExtend
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.CloudCopies.equality_step _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.PortCSP.blend_bad _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_rfl _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.badCount_cons _root_.OAI.MetricKMedian.PCP.PortGraph.blend_step _root_.OAI.MetricKMedian.PCP.PortGraph.countMean_zero _root_.OAI.MetricKMedian.PCP.PortGraph.edgeHit_sq _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_false _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_true _root_.OAI.MetricKMedian.PCP.PortGraph.propagate_succ _root_.OAI.MetricKMedian.PCP.PortGraph.propagate_zero _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step _root_.OAI.MetricKMedian.PCP.Walsh.cayley_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPGraphExtend

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace PortCSP
variable {V W D A : Type} [Fintype V] [Fintype D] [DecidableEq W] [DecidableEq D]
  [Fintype A] [DecidableEq A]
variable {G : PortGraph V D} (C : PortCSP G A) (e : V ↪ W)

omit [DecidableEq A] in
lemma extendedAllowed_outside (p : W × D) (hp : p.1 ∉ Set.range e) :
    C.extendedAllowed e p=univ := by
  rw [extendedAllowed,dite_eq_right (fun h => hp ((PortGraph.portEmbed_range e p).mp h))]

noncomputable def extend : PortCSP (G.extend e) A where
  allowed := C.extendedAllowed e
  symmetric := by
    intro p a b
    by_cases hp : p.1 ∈ Set.range e
    · obtain ⟨v,hv⟩ := hp
      have he : p=(e v,p.2) := Prod.ext hv.symm rfl
      rw [he,G.extend_rotate_image e (v,p.2),C.extendedAllowed_image e (G.rotate (v,p.2)),
        C.extendedAllowed_image e (v,p.2)]
      exact C.symmetric (v,p.2) a b
    · rw [G.extend_rotate_outside e p hp,C.extendedAllowed_outside e p hp]
      simp

omit [DecidableEq A] in
@[simp] lemma extend_bad_image (a : W → A) (p : V × D) :
    (C.extend e).Bad a (e p.1,p.2) ↔ C.Bad (a ∘ e) p := by
  unfold Bad
  rw [G.extend_step_image]
  change (a (e p.1),a (e (G.step p.1 p.2))) ∉ C.extendedAllowed e (e p.1,p.2) ↔ _
  rw [extendedAllowed_image]
  rfl

end PortCSP
end MetricKMedian.PCP

end Inline_PCPGraphExtend

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_CSPMix
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.CloudCopies.equality_step _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.PortCSP.extend_bad_image _root_.OAI.MetricKMedian.PCP.PortCSP.extendedAllowed_image _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_rfl _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.badCount_cons _root_.OAI.MetricKMedian.PCP.PortGraph.countMean_zero _root_.OAI.MetricKMedian.PCP.PortGraph.edgeHit_sq _root_.OAI.MetricKMedian.PCP.PortGraph.extend_rotate_image _root_.OAI.MetricKMedian.PCP.PortGraph.extend_step_image _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_false _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_true _root_.OAI.MetricKMedian.PCP.PortGraph.relabel_step _root_.OAI.MetricKMedian.PCP.PortGraph.square_step _root_.OAI.MetricKMedian.PCP.PortGraph.zigzag_step _root_.OAI.MetricKMedian.PCP.Walsh.cayley_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCSPMix

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace PortCSP
variable {V D A : Type} [Fintype A] [DecidableEq A] (G : PortGraph V D)

omit [DecidableEq A] in
@[simp] lemma always_complete (a : V → A) : (always (A := A) G).Satisfies a := by
  intro v d
  exact mem_univ _

omit [DecidableEq A] in
@[simp] lemma always_bad (a : V → A) (p : V × D) : ¬(always (A := A) G).Bad a p := by
  simp [Bad,always]

end PortCSP
end MetricKMedian.PCP

end Inline_PCPCSPMix

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_RegularizationObjects
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.BinaryCSP.mapLabels_allowed _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_rfl _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_false _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRegularizationObjects

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace CloudCopies
variable {V E A : Type} [Fintype E] [Fintype A] [DecidableEq A]
variable (C : BinaryCSP V E A)

def dartGraph : PortGraph (Dart (E := E)) Unit where
  rotate := dartFlip.prodCongr (Equiv.refl Unit)
  involutive := by rintro ⟨⟨e,b⟩,u⟩; simp [dartFlip]

def dartCSP : PortCSP (dartGraph (E := E)) A where
  allowed p := univ.filter (fun q => if p.1.2 then (q.2,q.1) ∈ C.allowed p.1.1
    else q ∈ C.allowed p.1.1)
  symmetric := by
    rintro ⟨⟨e,b⟩,u⟩ a b'
    cases b <;> simp [dartGraph,dartFlip]

noncomputable def equalityCSP : PortCSP (equalityGraph C) A where
  allowed _ := univ.filter (fun q => q.1=q.2)
  symmetric _ a b := by simp [eq_comm]

@[simp] lemma equality_bad (a : Node C → A) (v : Active C) (w : Copy C v)
    (d : ExpanderFamily.Degree) :
    (equalityCSP C).Bad a (⟨v,w⟩,d) ↔
      a ⟨v,w⟩ ≠ a ⟨v,(ExpanderFamily.graph (depth C v)).step w d⟩ := by
  simp [PortCSP.Bad,equalityCSP]

abbrev RegularPort := PortGraph.BlendPort (D := Unit) (S := ExpanderFamily.Degree)

def honest (x : V → A) (n : Node C) : A := x n.1.val

omit [Fintype A] [DecidableEq A] in
@[simp] lemma honest_dart (x : V → A) (d : Dart (E := E)) :
    honest C x (dartEmbed C d)=x (endpoint C d) := rfl

end CloudCopies
end MetricKMedian.PCP

end Inline_PCPRegularizationObjects

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_RegularizationSound
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRegularizationSound

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace CloudCopies
variable {V E A : Type} [Fintype E] [Fintype A] [DecidableEq A]
  [Inhabited A] [Nonempty E]
variable (C : BinaryCSP V E A) (a : Node C → A)

def Disagrees (n : Node C) : Prop := a n ≠ decoded C a n.1.val

end CloudCopies
end MetricKMedian.PCP

end Inline_PCPRegularizationSound

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_GlobalRegularization
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
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

noncomputable def depth := ExpanderFamily.level (Fintype.card (CloudCopies.Node C)-1)
abbrev Node := ExpanderFamily.Vertex (depth C)
abbrev FastPort := ExpanderFamily.Degree × ExpanderFamily.Degree
abbrev StrongPort := FastPort × FastPort
abbrev Degree := PortGraph.BlendPort (D := CloudCopies.RegularPort) (S := StrongPort)

omit [Fintype A] [DecidableEq A] [Inhabited A] in
lemma node_lower : Fintype.card (CloudCopies.Node C) ≤ Fintype.card (Node C) := by
  have h := ExpanderFamily.padding_lower (Fintype.card (CloudCopies.Node C)-1)
  have hp := Fintype.card_pos (α := CloudCopies.Node C)
  simp only [← Nat.card_eq_fintype_card] at hp
  simpa only [Node,depth,← Nat.card_eq_fintype_card,Nat.sub_add_cancel hp] using h

noncomputable def strong : PortGraph (Node C) StrongPort :=
  (ExpanderFamily.graph (depth C)).square.square

end GlobalRegularization
end MetricKMedian.PCP

end Inline_PCPGlobalRegularization

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_Amplifier
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAmplifier

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace Amplifier
abbrev Degree := GlobalRegularization.Degree
abbrev Bits := Advice.BitIndex Degree (Fin 4) radius
noncomputable instance bitsFintype : Fintype Bits := inferInstance
noncomputable instance bitsDecidableEq : DecidableEq Bits := Classical.decEq _
noncomputable instance edgeSampleFintype : Fintype (AlphabetReduction.EdgeSample Bits) := inferInstance

variable {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
variable (C : BinaryCSP V E Label)
abbrev Node := GlobalRegularization.Node C
noncomputable instance nodeFintype : Fintype (Node C) := inferInstance

end Amplifier
end MetricKMedian.PCP

end Inline_PCPAmplifier

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_AmplifierSize
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAmplifierSize

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace Amplifier
abbrev WalkData := (Fin radius → Fin (steps+1)) × (Fin radius → Degree)
@[irreducible] noncomputable def walkCoeff : ℕ := Nat.card WalkData
scoped notation "edgeCoefficient" => (walkCoeff*nodeCoeff*(4*Nat.card (AlphabetReduction.EdgeSample Bits)))
scoped notation "sizeCoefficient" => (nodeCoeff*Nat.card (BitVector Bits)+
  walkCoeff*nodeCoeff*(AlphabetReduction.interiorBound Bits+Nat.card (AlphabetReduction.EdgeSample Bits))+edgeCoefficient)

end Amplifier
end MetricKMedian.PCP

end Inline_PCPAmplifierSize

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_FlexibleCloud
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.BinaryCSP.mapLabels_allowed _root_.OAI.MetricKMedian.PCP.Compiler.RotationTable.table_length _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_end _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_port _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_rfl _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_start _root_.OAI.MetricKMedian.PCP.PortGraph.Walk.cast_vertex _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_false _root_.OAI.MetricKMedian.PCP.PortGraph.incidence_source_true
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFlexibleCloud

namespace MetricKMedian.PCP
open Finset CloudCopies
open scoped BigOperators Classical

namespace FlexibleCloud
variable {V E A : Type} [Fintype V] [Fintype E]
variable (C : BinaryCSP V E A)
variable (embed : ∀ v : Active C, Incident C v ↪ Copy C v)

noncomputable def dartEmbed : Dart (E := E) ↪ Node C where
  toFun d := ⟨owner C d, embed (owner C d) ⟨d,rfl⟩⟩
  inj' := by
    intro d e h
    have ho : owner C d=owner C e := congrArg Sigma.fst h
    have hh : (⟨owner C d,⟨d,rfl⟩⟩ : (v : Active C) × Incident C v) =
        ⟨owner C e,⟨e,rfl⟩⟩ := by
      apply (Function.Embedding.sigmaMap (Function.Embedding.refl _) (embed)).injective
      exact h
    exact congrArg (fun p : (v : Active C) × Incident C v => p.2.val) hh

variable [Fintype A] [DecidableEq A]

noncomputable def matchingGraph : PortGraph (Node C) Unit := dartGraph.extend (dartEmbed C embed)
noncomputable def matchingCSP : PortCSP (matchingGraph C embed) A := (dartCSP C).extend (dartEmbed C embed)

omit [Fintype V] in
@[simp] lemma matching_bad (a : Node C → A) (e : E) :
    (matchingCSP C embed).Bad a (dartEmbed C embed (e,false),()) ↔
      (a (dartEmbed C embed (e,false)),a (dartEmbed C embed (e,true))) ∉ C.allowed e := by
  change ((dartCSP C).extend (dartEmbed C embed)).Bad a (dartEmbed C embed (e,false),()) ↔ _
  rw [PortCSP.extend_bad_image (dartCSP C) (dartEmbed C embed) a ((e,false),())]
  simp [PortCSP.Bad,dartCSP,dartGraph,PortGraph.step,dartFlip]

abbrev RegularPort := PortGraph.BlendPort (D := Unit) (S := ExpanderFamily.Degree)
noncomputable def regularGraph : PortGraph (Node C) RegularPort := (matchingGraph C embed).blend (equalityGraph C)
noncomputable def regularCSP : PortCSP (regularGraph C embed) A := (matchingCSP C embed).blend (equalityCSP C)

omit [Fintype V] [Fintype A] [DecidableEq A] in
@[simp] lemma honest_dart (x : V → A) (d : Dart (E := E)) :
    honest C x (dartEmbed C embed d)=x (endpoint C d) := rfl

end FlexibleCloud
end MetricKMedian.PCP

end Inline_PCPFlexibleCloud

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_FlexibleRegularization
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

noncomputable def padded : PortCSP ((FlexibleCloud.regularGraph C cloudEmbed).extend padEmbed) A :=
  (FlexibleCloud.regularCSP C cloudEmbed).extend padEmbed
noncomputable def graph : PortGraph (Node C) Degree :=
  ((FlexibleCloud.regularGraph C cloudEmbed).extend padEmbed).blend (strong C)
noncomputable def csp : PortCSP (graph C cloudEmbed padEmbed) A :=
  (padded C cloudEmbed padEmbed).blend (PortCSP.always (strong C))

end FlexibleRegularization
end MetricKMedian.PCP

end Inline_PCPFlexibleRegularization

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_FlexibleAmplifier
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
abbrev Node := GlobalRegularization.Node C
abbrev Edge := PortCSP.PowerEdge (G := FlexibleRegularization.graph C cloudEmbed padEmbed) steps radius
noncomputable instance nodeFintype : Fintype (Node C) := inferInstance

end FlexibleAmplifier
end MetricKMedian.PCP

end Inline_PCPFlexibleAmplifier

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_RegularGraphLaws
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
noncomputable abbrev padGraph := (FlexibleCloud.regularGraph C cloudEmbed).extend padEmbed
end MetricKMedian.PCP.FlexibleRegularization

end Inline_PCPRegularGraphLaws

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_RegularPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRegularPrograms
namespace MetricKMedian.PCP.Compiler.RegularProgram
open Binary Binary.Automatic CloudProgram RotationTable
open scoped Classical

variable {A : Type} [Fintype A]
abbrev RPort := CloudCopies.RegularPort
abbrev Port := GlobalRegularization.Degree
end MetricKMedian.PCP.Compiler.RegularProgram

end Inline_PCPRegularPrograms

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_CloudOrder
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.BinaryCSP.mapLabels_allowed _root_.OAI.MetricKMedian.PCP.FlexibleCloud.honest_dart _root_.OAI.MetricKMedian.PCP.FlexibleCloud.matching_bad _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.PortCSP.powered_allowed
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
noncomputable def dartOrder : Ordered (CloudCopies.Dart (E := E)) := eo.prod boolOrder
noncomputable def activeOrder : Ordered (CloudCopies.Active C) := by
  classical
  exact @Ordered.filter V vo (fun v => v ∈ Set.range (CloudCopies.endpoint C)) (Classical.decPred _)
noncomputable def incidentOrder (v : CloudCopies.Active C) : Ordered (CloudCopies.Incident C v) :=
  (dartOrder eo).filter (fun d => CloudCopies.owner C d=v)
noncomputable def copyOrder (v : CloudCopies.Active C) : Ordered (CloudCopies.Copy C v) :=
  (Ordered.fin _).map (ExpanderFamily.vertexEquiv (CloudCopies.depth C v)).symm
noncomputable def nodeOrder : Ordered (CloudCopies.Node C) :=
  (activeOrder C vo).sigma (copyOrder C)
lemma copy_index_bound (v : CloudCopies.Active C) : (incidentOrder C eo v).entries.length ≤
    (Fintype.card ExpanderFamily.Branch)^(CloudCopies.depth C v) := by
  rw [Ordered.length_card]
  have h := CloudCopies.copy_card_lower C v
  have he := Fintype.card_congr (ExpanderFamily.vertexEquiv (CloudCopies.depth C v))
  simp only [Fintype.card_fin] at he
  simp only [← Nat.card_eq_fintype_card] at h he ⊢
  exact h.trans_eq he
noncomputable def cloudEmbed (v : CloudCopies.Active C) : CloudCopies.Incident C v ↪ CloudCopies.Copy C v :=
  (incidentOrder C eo v).equiv.toEmbedding.trans
    ((Fin.castLEEmb (copy_index_bound C eo v)).trans (ExpanderFamily.vertexEquiv _).symm.toEmbedding)
@[simp] lemma cloudEmbed_index (v : CloudCopies.Active C) (d : CloudCopies.Incident C v) :
    (ExpanderFamily.vertexEquiv _ (cloudEmbed C eo v d)).val=(incidentOrder C eo v).entries.idxOf d := by
  simp only [cloudEmbed,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,
    Equiv.apply_symm_apply,Fin.castLEEmb_apply,Fin.val_castLE,Ordered.equiv_val]
  simp only [List.idxOf]
  congr 1
  funext x
  simp only [Bool.beq_eq_decide_eq]
noncomputable def nodeCode (p : CloudCopies.Node C) : ℕ × ℕ :=
  ((vo.equiv p.1.val).val,(ExpanderFamily.vertexEquiv _ p.2).val)
variable [Nonempty E]
omit [DecidableEq E] in
lemma pad_index_bound : (nodeOrder C vo).entries.length ≤
    (Fintype.card ExpanderFamily.Branch)^(GlobalRegularization.depth C) := by
  rw [Ordered.length_card]
  have h := GlobalRegularization.node_lower C
  have he := Fintype.card_congr (ExpanderFamily.vertexEquiv (GlobalRegularization.depth C))
  simp only [Fintype.card_fin] at he
  simp only [← Nat.card_eq_fintype_card] at h he ⊢
  exact h.trans_eq he
noncomputable def padEmbed : CloudCopies.Node C ↪ GlobalRegularization.Node C :=
  (nodeOrder C vo).equiv.toEmbedding.trans
    ((Fin.castLEEmb (pad_index_bound C vo)).trans (ExpanderFamily.vertexEquiv _).symm.toEmbedding)
end MetricKMedian.PCP.Compiler.CloudOrder

end Inline_PCPCloudOrder

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_CloudSpec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCloudSpec
namespace MetricKMedian.PCP.Compiler.CloudSpec
open scoped Classical
open CloudProgram CloudOrder

variable {A : Type}
variable (t : CSPTable A) (h : t.WellFormed)
lemma fin_equiv_val (n : ℕ) (dec : DecidableEq (Fin n)) (i : Fin n) :
    (@Ordered.equiv (Fin n) dec (Ordered.fin n) i).val=i.val := by
  have hg := @Ordered.get_equiv (Fin n) dec (Ordered.fin n) i
  change (List.finRange n)[(@Ordered.equiv (Fin n) dec (Ordered.fin n) i).val]=i at hg
  simpa only [List.getElem_finRange,Fin.val_cast] using congrArg Fin.val hg
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPCloudSpec

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_NearestFillingFormula
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation
open Finset
variable {n : ℕ}

theorem fill_formula (U : Finset (Fin n)) (y d : Fin n → ℚ) (t : ℚ)
    (hy : ∀ i∈U, 0 ≤ y i) (ht : 0 ≤ t) (hm : t ≤ ∑ i∈U, y i) (i : Fin n) :
    (fill U y d t hy ht hm).amount i=
      if i∈U then min (y i) (max 0 (t-priorMass U y d i)) else 0 := by
  revert t hy
  refine U.strongInductionOn ?_
  intro U ih t hy ht hm
  by_cases hi : i∈U
  · have hU : U.Nonempty := ⟨i,hi⟩
    let a := firstNearest U d hU
    have ha : a∈U := (firstNearest_spec U d hU).1
    have hpref : priorMass U y d a=0 := priorMass_first U y d hU
    rw [ite_eq_left hi]
    by_cases hs : t ≤ y a
    · rw [fill]
      have hs' : t ≤ y (firstNearest U d hU) := hs
      simp only [dite_eq_left hU,dite_eq_left hs']
      change (if i=a then t else 0)=min (y i) (max 0 (t-priorMass U y d i))
      by_cases he : i=a
      · subst i
        rw [ite_eq_left rfl,hpref,sub_zero,max_eq_right ht,min_eq_right hs]
      · rw [ite_eq_right he]
        have hp := priorMass_nonneg (U.erase a) y d i (fun j hj => hy j (mem_of_mem_erase hj))
        rw [priorMass_erase U y d a i ha (first_before U d hU i hi he)]
        rw [max_eq_left (by linarith),min_eq_right (hy i hi)]
    · rw [fill]
      have hs' : ¬t ≤ y (firstNearest U d hU) := hs
      simp only [dite_eq_left hU,dite_eq_right hs']
      by_cases he : i=a
      · subst i
        change @Function.update (Fin n) (fun _ => ℚ) _ _ a (y a) a = _
        simp only [Function.update_self,hpref,sub_zero,max_eq_right ht,min_eq_left (le_of_not_ge hs)]
      · rw [Function.update_of_ne he]
        rw [ih (U.erase a) (erase_ssubset ha)]
        rw [ite_eq_left (mem_erase.mpr ⟨he,hi⟩)]
        rw [priorMass_erase U y d a i ha (first_before U d hU i hi he)]
        congr 2
        ring
  · rw [ite_eq_right hi]
    exact (fill U y d t hy ht hm).outside i hi

 theorem computedNearest_formula (y d : Fin n → ℚ) (hy : ∀ i, 0 ≤ y i) (hm : 1 ≤ ∑ i, y i) (i : Fin n) :
    (computedNearest y d hy hm)[i.val]=min (y i) (max 0 (1-priorMass univ y d i)) := by
  simp only [computedNearest,Vector.getElem_ofFn,fill_formula,mem_univ,ite_true]
end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_IterationPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPIterationPolynomial

namespace MetricKMedian.PCP
open scoped Classical BigOperators

namespace Amplifier
lemma log_power_bound (c e : ℕ) (he : 0<e) : c^(Nat.log 2 e) ≤ e^c := by
  calc
    _ ≤ (2^c)^(Nat.log 2 e) := Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) _
    _ = (2^(Nat.log 2 e))^c := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
    _ ≤ e^c := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (Nat.ne_of_gt he)) _
end Amplifier
end MetricKMedian.PCP

end Inline_PCPIterationPolynomial

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_MatchingLaws
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
variable [Fintype A] [DecidableEq A]
lemma matching_allowed_image (d : CloudCopies.Dart (E := E)) :
    (matchingCSP C embed).allowed (dartEmbed C embed d,())=(CloudCopies.dartCSP C).allowed (d,()) := by
  exact (CloudCopies.dartCSP C).extendedAllowed_image (dartEmbed C embed) (d,())
lemma matching_allowed_outside (p : CloudCopies.Node C) (hp : p∉Set.range (dartEmbed C embed)) :
    (matchingCSP C embed).allowed (p,())=Finset.univ := by
  exact (CloudCopies.dartCSP C).extendedAllowed_outside (dartEmbed C embed) (p,()) hp
end MetricKMedian.PCP.FlexibleCloud

end Inline_PCPMatchingLaws

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_DualListCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.LPBinary.Program
open Binary Binary.PolyProgram Function

noncomputable def candidatesProgram : PolyProgram (encodePair er Ratio.encode) er (fun x : Row × ℚ => Dual.candidates x.1 x.2) := by
  let consH := (exchange er Ratio.encode).comp (listCons Ratio.encode)
  exact (((constant (encodePair er Ratio.encode) Ratio.encode 0).fanout consH).comp (listCons Ratio.encode)).congr _ (fun _ => rfl)

end MetricKMedian.LPBinary.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_IntegralFractionalComparison
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset ProjectedSubgradient
variable {n m : ℕ} [NeZero n] [NeZero m]

omit [NeZero n] [NeZero m] in

theorem integral_comparison (d : Fin m → Fin n → ℚ) (k : ℕ)
    (hd : ∀ j i, 0 ≤ d j i) (S : Finset (Fin n)) (hS : S.Nonempty)
    (hSk : S.card ≤ k) (a : Fin m → Fin n) (ha : ∀ j, a j ∈ S)
    (hc : (∑ j, d j (a j)) ≤ 1) (H : ℚ) :
    ∃ z : Fin n → ℚ, feasible (k:ℚ) z ∧ objective d z H ≤ ∑ j, d j (a j) := by
  classical
  obtain ⟨i₀,hi₀⟩ := hS
  let z : Fin n → ℚ := fun i => (if i ∈ S then 1 else 0)+
    (if i=i₀ then (k:ℚ)-(S.card:ℚ) else 0)
  have hrest : (0:ℚ) ≤ (k:ℚ)-(S.card:ℚ) := by
    have hh : (S.card:ℚ) ≤ k := by exact_mod_cast hSk
    linarith
  have hz0 : ∀ i, 0 ≤ z i := by
    intro i
    dsimp [z]
    split_ifs <;> linarith
  have hzs : (∑ i, z i)=(k:ℚ) := by
    simp only [z,sum_add_distrib,sum_ite_mem,sum_const,nsmul_eq_mul,
      sum_ite_eq',mem_univ,ite_true]
    simp
  have hza : ∀ j, 1 ≤ z (a j) := by
    intro j
    dsimp [z]
    rw [ite_eq_left (ha j)]
    split_ifs <;> linarith
  let x : Fin m → Fin n → ℚ := fun j i => if i=a j then 1 else 0
  have hx : ∀ j i, 0 ≤ x j i ∧ x j i ≤ z i := by
    intro j i
    dsimp [x]
    by_cases he : i=a j
    · rw [ite_eq_left he,he]; exact ⟨by norm_num,hza j⟩
    · rw [ite_eq_right he]; exact ⟨le_rfl,hz0 i⟩
  have hs : ∀ j, ∑ i, x j i=1 := by intro j; simp [x]
  have edge : ∀ j, d j (a j) ≤ 1 := by
    intro j
    exact (single_le_sum (fun j _ => hd j (a j)) (mem_univ j)).trans hc
  refine ⟨z,⟨hz0,hzs⟩,(objective_le_assignment d z x H hx hs).trans_eq ?_⟩
  apply sum_congr rfl
  intro j _
  simp only [x,ite_mul,one_mul,zero_mul,sum_ite_eq',mem_univ,ite_true,
    truncated,ite_eq_left (edge j)]

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_NearestListProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset

namespace Nearest

theorem filling_ofFn {n : ℕ} (y d : Fin n → ℚ) (hy : ∀ i, 0 ≤ y i) (hm : 1 ≤ ∑ i, y i) :
    filling (List.ofFn y) (List.ofFn d)=List.ofFn (ProjectedSubgradient.point (Preparation.computedNearest y d hy hm)) := by
  simp only [filling,entries_ofFn,List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply,amount,prior_ofFn,ProjectedSubgradient.point,Preparation.computedNearest_formula]

end Nearest
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β γ : Type}

theorem prod_property (μ : SparseIntegerLaw α) (ν : SparseIntegerLaw β)
    (f : α → β → γ) (P : γ → Prop)
    (hP : ∀ a : Fin μ.length, ∀ b : Fin ν.length, P (f μ.states[a.val] ν.states[b.val])) :
    ∀ a : Fin (μ.prod ν f).length, P (μ.prod ν f).states[a.val] := by
  intro a
  change P ((Vector.ofFn (fun i => f μ.states[((finProdFinEquiv (m := μ.length) (n := ν.length)).symm i).1.val]
    ν.states[((finProdFinEquiv (m := μ.length) (n := ν.length)).symm i).2.val]))[a.val])
  simp only [Vector.getElem_ofFn]
  exact hP _ _

end MetricKMedian.SparseIntegerLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_FractionalInputProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.FractionalRefinement.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram

def Input.unit (z : Input) : RationalUnitInput.Program.Input :=
  ⟨count z.a z.k z.ha z.hj z.dc,z.j,unitInput z.a z.k z.ha z.hj z.dc z.dd z.df z.hdc z.hdd z.hds⟩
end MetricKMedian.Preparation.FractionalRefinement.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CountStepProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.SparseCounts.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.DependentProgram SparseIntegerLaw.BinarySparse
open ListOperation (Row Table er et)
abbrev State := Bundle T

def State.product (x : State) : State := ⟨x.ctx,x.law.prod (column x.ctx) (update x.ctx)⟩

def State.increment (x : State) : State := ⟨⟨x.ctx.input,x.ctx.t+1⟩,x.law⟩
end MetricKMedian.SparseCounts.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CountRunProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseCounts.Program
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.DependentProgram SparseIntegerLaw.BinarySparse
open ListOperation (Row Table et)
def Input.start (x : Input) : State := ⟨⟨x,0⟩,.dirac (fun _ _ => 0)⟩

end MetricKMedian.SparseCounts.Program
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

def State.last (x : RoundingProgram.State false) : RoundingProgram.State false :=
  ⟨x.n,x.β,x.positive,x.μ.branch RationalLastFraction.probability RationalLastFraction.probability_unit RationalLastFraction.endpoint⟩
end MetricKMedian.RoundingProgram.WeightedRound
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_SignedTerminalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
open Binary.Automatic Binary.Automatic.Poly
namespace Terminal

abbrev ber := SparseBernoulli.Program.er

end Terminal
end MetricKMedian.RoundingProgram
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
def Input.unit (x : Input) : Program.Input := ⟨x.f,x.j,x.U⟩
end MetricKMedian.Preparation.RationalUnitInput.ScanProgram
end

end OAI
end


