-- Prove2me | Definitions.Def_OAIQ053K067
-- name    : OAIQ053K067
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:17:32.720992+00:00
-- url     : https://prove2.me/theorems/39114218-56b6-4fc9-be5c-1b75d61142bd
-- title:
--   Definitions bundle OAIQ053K067 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 65 declarations of OpenAI's Lean: 26 definitions and 39 theorems. The definitions and types are `OAI.MetricKMedian.PCP.Compiler.AmplifierProgram.State`, `OAI.MetricKMedian.PCP.Compiler.AmplifierProgram.bits`, `OAI.MetricKMedian.PCP.Compiler.AmplifierProgram.fallback`, `OAI.MetricKMedian.PCP.Compiler.AmplifierProgram.generate`, `OAI.MetricKMedian.PCP.Compiler.AmplifierProgram.guarded`, `OAI.MetricKMedian.PCP.Compiler.AmplifierProgram.iterate`, `OAI.MetricKMedian.PCP.Compiler.AmplifierProgram.next`, `OAI.MetricKMedian.PCP.Compiler.AmplifierProgram.normalize`, `OAI.MetricKMedian.PCP.Compiler.AmplifierProgram.power`, `OAI.MetricKMedian.PCP.Compiler.AmplifierProgram.rawCo`, `OAI.MetricKMedian.PCP.Compiler.AmplifierProgram.schedule`, `OAI.MetricKMedian.PCP.Compiler.CSPTable.sizeBound`, `OAI.MetricKMedian.PCP.Compiler.CloudSpec.EO`, `OAI.MetricKMedian.PCP.Compiler.CloudSpec.VO`, `OAI.MetricKMedian.PCP.Compiler.CloudSpec.dartCode`, `OAI.MetricKMedian.PCP.Compiler.InitialProgram.represents`, `OAI.MetricKMedian.PCP.Compiler.PowerProgram.seeds`, `OAI.MetricKMedian.PCP.Compiler.PowerProgram.table`, `OAI.MetricKMedian.PCP.Compiler.RegularProgram.rotate`, `OAI.MetricKMedian.PCP.Compiler.SeedProgram.legal`, `OAI.MetricKMedian.Preparation.RationalBundles.Program.view`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.Input.encode`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.Input.raw`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.State.encode`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.State.raw`, `OAI.MetricKMedian.RoundingProgram.Terminal.bernoulliInputProgram`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Amplification_AmplifierCompiler`, `KMedian_Amplification_AmplifierGuard`, `KMedian_Amplification_AmplifierIteration`, `KMedian_Amplification_AmplifierProgram`, `KMedian_Amplification_AmplifierTableSize`, `KMedian_Amplification_PowerPrograms`, `KMedian_Amplification_PowerTable`, `KMedian_Amplification_RegularPrograms`, `KMedian_CookLevin_InitialTable`, `KMedian_Expanders_CloudSpec`, `KMedian_Machines_CSPTableBounds`, `KMedian_Machines_LocalCompiler`, `KMedian_Machines_RawSquare`, `KMedian_Machines_RawWalk`, `KMedian_Machines_TableCounts`, `KMedian_Preparation_RepresentativeProgram`, `KMedian_Programs_BundleGeometryProgram`, `KMedian_Programs_LastFractionProgram`, `KMedian_Projection_RepairProgram`, `KMedian_Rounding_SignedTerminalProgram`.
--
--   **Imports.** It imports the bundles `OAIQ053K054`, `OAIQ053K055`, `OAIQ053K056`, `OAIQ053K058`, `OAIQ053K059` and `OAIQ053K060` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K073` and `OAIQ053K074`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K054
import Definitions.Def_OAIQ053K055
import Definitions.Def_OAIQ053K056
import Definitions.Def_OAIQ053K058
import Definitions.Def_OAIQ053K059
import Definitions.Def_OAIQ053K060

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_RawWalk
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.relationCoding _root_.OAI.MetricKMedian.PCP.Compiler.relationHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRawWalk
namespace MetricKMedian.PCP.Compiler.RawWalk
open Binary Binary.Automatic
open scoped Classical

variable {T D A : Type} [Coding T] [Fintype D] [Coding D] [Hardcoded D] [Inhabited D]
variable (rotate : T → ℕ → D → ℕ × D)
variable (hp : Poly (fun p : (T × ℕ) × D => rotate p.1.1 p.1.2 p.2))
include hp
omit [Hardcoded D] in
lemma poly_vertex (cap : ℕ) : Poly (fun p : ((T × ℕ) × (Fin cap → D)) × Fin (cap+1) =>
    vertexAt rotate cap p.1.1.1 p.1.1.2 p.1.2 p.2.val) := by
  have hf := poly_finite_cases (fun i : Fin (cap+1) => fun p : (T × ℕ) × (Fin cap → D) =>
    vertexAt rotate cap p.1.1 p.1.2 p.2 i.val) (fun i => poly_at rotate hp cap i.val)
  exact hf.comp (Poly.pair Poly.snd Poly.fst)
end MetricKMedian.PCP.Compiler.RawWalk

end Inline_PCPRawWalk

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PowerPrograms
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPowerPrograms
namespace MetricKMedian.PCP.Compiler.PowerProgram
open Binary Binary.Automatic
open scoped Classical

variable {T D A : Type} [Coding T] [Fintype D] [Coding D] [Hardcoded D] [Inhabited D]
  [Fintype A] [DecidableEq A] [Inhabited A]
variable (rot : T → ℕ → D → ℕ × D) (allow : T → ℕ → D → Finset (A × A))
variable (hr : Poly (fun s : (T × ℕ) × D => rot s.1.1 s.1.2 s.2))
  (ha : Poly (fun s : (T × ℕ) × D => allow s.1.1 s.1.2 s.2))
include hr ha in
omit [DecidableEq A] in
lemma poly_row (t cap : ℕ) : Poly (fun p : (T × ℕ) × Tag (D := D) t cap => row rot allow t cap p.1.1 p.1.2 p.2) := by
  have hs : Poly (fun c : Fin cap → Fin (t+1) => stop t cap c) := hardcoded _
  have hw : Poly (fun p : (T × ℕ) × Tag (D := D) t cap => (p.1,p.2.2)) := by fun_prop
  have hn := hs.comp (Poly.fst.comp Poly.snd : Poly (fun p : (T × ℕ) × Tag (D := D) t cap => p.2.1))
  have hv := (RawWalk.poly_vertex rot hr cap).comp (Poly.pair hw hn)
  have hb := (RawWalk.poly_backs rot hr cap).comp hw
  have hl := (poly_rels rot allow hr ha cap).comp hw
  have hc : Poly (fun q : (Fin (cap+1) × (Fin cap → D)) × ((Fin cap → D) × (Fin cap → Finset (A × A))) =>
    relation cap q.1.1 q.1.2 q.2.1 q.2.2) := hardcoded _
  have hrel := hc.comp (Poly.pair (Poly.pair hn (Poly.snd.comp Poly.snd)) (Poly.pair hb hl))
  exact Poly.pair (Poly.snd.comp Poly.fst) (Poly.pair hv hrel)
end MetricKMedian.PCP.Compiler.PowerProgram

end Inline_PCPPowerPrograms

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
abbrev VO := Ordered.fin t.1.length
abbrev EO := Ordered.fin t.2.length
def dartCode (d : CloudCopies.Dart (E := Fin t.2.length)) : Dart := (d.1.val,d.2)
lemma dartCode_injective : Function.Injective (dartCode t) := by
  rintro ⟨e,b⟩ ⟨f,c⟩ hh
  have he : e=f := Fin.ext (congrArg Prod.fst hh)
  have hb : b=c := congrArg Prod.snd hh
  subst f; subst c; rfl
lemma darts_eq : darts t=((dartOrder (EO t)).entries.map (dartCode t)) := by
  unfold darts dartOrder Ordered.prod EO Ordered.fin boolOrder
  simp only [List.product,List.map_flatMap,List.map_cons,List.map_nil]
  rw [← finRange_val t.2.length,List.flatMap_map]
  rfl
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPCloudSpec

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_RawSquare
attribute [-instance] _root_.OAI.MetricKMedian.PCP.PortCSP.badDecidable _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRawSquare
namespace MetricKMedian.PCP.Compiler.RotationTable
open Binary Binary.Automatic

variable {D : Type} [Fintype D] [Inhabited D]
variable [Coding D] [Hardcoded D]
omit [Coding D] [Hardcoded D]
lemma squareLookup_table {V : Type} {N : ℕ} (G : PortGraph V D) (e : V ≃ Fin N) (v : V) (d : D × D) :
    squareLookup (table G e) (e v).val d=((e (G.square.step v d)).val,G.square.back v d) := by
  simp only [squareLookup,lookup_table]
  rfl
lemma fourthLookup_table {V : Type} {N : ℕ} (G : PortGraph V D) (e : V ≃ Fin N) (v : V) (d : (D × D) × (D × D)) :
    fourthLookup (table G e) (e v).val d=((e (G.square.square.step v d)).val,G.square.square.back v d) := by
  simp only [fourthLookup,squareLookup_table]
  rfl
end MetricKMedian.PCP.Compiler.RotationTable

end Inline_PCPRawSquare

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_RegularPrograms
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
noncomputable def rotate (t : CSPTable A) (v : ℕ) (d : Port) : ℕ × Port :=
  if d.1=0 then
    let q := paddedRotate t v d.2.1
    (q.1,(d.1,(q.2,d.2.2)))
  else
    let q := strongRotate t v d.2.2
    (q.1,(d.1,(d.2.1,q.2)))
@[fun_prop] lemma poly_rotate : Poly (fun s : (CSPTable A × ℕ) × Port => rotate s.1.1 s.1.2 s.2) := by
  exact poly_blendProgram (fun p : CSPTable A × ℕ => paddedRotate p.1 p.2)
    (fun p : CSPTable A × ℕ => strongRotate p.1 p.2) poly_paddedRotate poly_strongRotate
@[fun_prop] lemma poly_allowed : Poly (fun s : (CSPTable A × ℕ) × Port => allowed s.1.1 s.1.2 s.2) := by
  unfold allowed
  apply Poly.ite_prop
  · exact poly_zeroBranch.comp (Poly.fst.comp Poly.snd)
  · exact poly_paddedAllowed.comp (Poly.pair Poly.fst (Poly.fst.comp (Poly.snd.comp Poly.snd)))
  · exact Automatic.Poly.const _
end MetricKMedian.PCP.Compiler.RegularProgram

end Inline_PCPRegularPrograms

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PowerTable
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPowerTable
namespace MetricKMedian.PCP.Compiler.PowerProgram
open Binary Binary.Automatic RegularProgram CloudSpec
open scoped Classical

variable {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
noncomputable def seeds (s : CSPTable A) : List Unit := (CloudProgram.global s).map (fun _ => ())
noncomputable def table (t cap : ℕ) (s : CSPTable A) : CSPTable (Advice Port A cap) :=
  CSPTable.grid (seeds s) (Ordered.fixed (Tag (D := Port) t cap)).entries
    (row RegularProgram.rotate RegularProgram.allowed t cap s)
omit [DecidableEq A] in
lemma poly_table (t cap : ℕ) : Poly (table (A := A) t cap) := by
  apply CSPTable.poly_grid
  · unfold seeds
    apply Poly.list_map (Automatic.Poly.const ()) CloudProgram.poly_global
  · exact poly_row RegularProgram.rotate RegularProgram.allowed RegularProgram.poly_rotate RegularProgram.poly_allowed t cap
end MetricKMedian.PCP.Compiler.PowerProgram

end Inline_PCPPowerTable

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_AmplifierProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAmplifierProgram
namespace MetricKMedian.PCP.Compiler.AmplifierProgram
open Amplifier Binary Binary.Automatic CloudSpec
open scoped Classical

noncomputable def power (s : CSPTable Label) := PowerProgram.table steps radius s
noncomputable def bits (s : CSPTable Label) : CSPTable (BitVector Bits) :=
  CSPTable.relabel (Advice.bitsEquiv Degree (Fin 4) radius) (power s)
noncomputable def next (s : CSPTable Label) : CSPTable Label := AlphabetProgram.table Bits (bits s)
lemma poly_bits : Poly bits := (CSPTable.poly_relabel _).comp (PowerProgram.poly_table steps radius)
lemma poly_next : Poly next := (AlphabetProgram.poly_table Bits).comp poly_bits
end MetricKMedian.PCP.Compiler.AmplifierProgram

end Inline_PCPAmplifierProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_TableCounts
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableCounts
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

namespace CSPTable
variable {A B : Type}
lemma grid_counts (v : List Unit) (b : List B) (r : ℕ → B → CSPRow A) :
    (grid v b r).1.length=v.length ∧ (grid v b r).2.length=v.length*b.length := by
  constructor
  · rfl
  · unfold grid
    rw [length_flatMap_uniform _ _ b.length (by intros; simp only [List.length_map]),List.length_range]
lemma rect_counts (v e : List Unit) (b : List B) (r : ℕ → B → CSPRow A) :
    (rect v e b r).1.length=v.length ∧ (rect v e b r).2.length=e.length*b.length := by
  constructor
  · rfl
  · unfold rect
    rw [length_flatMap_uniform _ _ b.length (by intros; simp only [List.length_map]),List.length_range]
end CSPTable
namespace PowerProgram
variable {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
omit [DecidableEq A] in
lemma counts (t cap : ℕ) (s : CSPTable A) :
    (table t cap s).1.length=(seeds s).length ∧
    (table t cap s).2.length=(seeds s).length*(Ordered.fixed (Tag (D := RegularProgram.Port) t cap)).entries.length :=
  CSPTable.grid_counts _ _ _
end PowerProgram
namespace AlphabetProgram
variable (K : Type) [Fintype K] [DecidableEq K]
lemma counts (s : CSPTable (BitVector K)) :
    (table K s).1.length=s.1.length*B K+s.2.length*I K+s.2.length*S K ∧
    (table K s).2.length=s.2.length*(Ordered.fixed (Tag K)).entries.length := by
  have h := CSPTable.rect_counts (seeds K s) (roots K s) (Ordered.fixed (Tag K)).entries (row K s)
  simpa only [table,seeds_length,roots,List.length_map] using h
end AlphabetProgram
end MetricKMedian.PCP.Compiler

end Inline_PCPTableCounts

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_AmplifierTableSize
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAmplifierTableSize
namespace MetricKMedian.PCP.Compiler.AmplifierProgram
open Amplifier Binary Binary.Automatic CloudSpec
open scoped Classical

noncomputable def rawCo (K : Type) [Fintype K] [DecidableEq K] (t cap : ℕ) : ℕ :=
  1+2*ExpanderFamily.growth^2*(AlphabetProgram.B K+
    (Ordered.fixed (PowerProgram.Tag (D := RegularProgram.Port) t cap)).entries.length*
      (AlphabetProgram.I K+AlphabetProgram.S K+(Ordered.fixed (AlphabetProgram.Tag K)).entries.length))
lemma rawCo_pos (K : Type) [Fintype K] [DecidableEq K] (t cap : ℕ) : 0 < rawCo K t cap :=
  Nat.add_pos_left Nat.zero_lt_one _
end MetricKMedian.PCP.Compiler.AmplifierProgram

end Inline_PCPAmplifierTableSize

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_CSPTableBounds
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCSPTableBounds
namespace MetricKMedian.PCP.Compiler.CSPTable
open Binary Binary.Automatic Finset
open scoped BigOperators Classical

variable {A : Type} [Fintype A] [DecidableEq A]
noncomputable def sizeBound (N : ℕ) : ℕ :=
  2*(N*(2*(enc ()).length+1))+1+N*(2*(2*(N+1)+1+(2*(N+1)+1+relationBound (A := A)))+1)
omit [DecidableEq A] in
lemma size_bound {s : CSPTable A} (h : s.WellFormed) (N : ℕ)
    (hN : s.1.length+s.2.length≤N) : (enc s).length≤ sizeBound (A := A) N := by
  have h1 : (enc s.1).length ≤ N*(2*(enc ()).length+1) := by
    apply (EncodedList.length_bound enc s.1 _ (by intros; exact Nat.le_refl _)).trans
    exact Nat.mul_le_mul_right _ (by omega)
  have he (r : CSPRow A) (hr : r∈s.2) :
      (enc r).length≤2*(N+1)+1+(2*(N+1)+1+relationBound (A := A)) := by
    have hh := h.2 r hr
    have hl : r.1.bits.length≤N+1 :=
      (NatBinary.length_le_height (Nat.lt_two_pow_self.le)).trans (by omega)
    have hr : r.2.1.bits.length≤N+1 :=
      (NatBinary.length_le_height (Nat.lt_two_pow_self.le)).trans (by omega)
    have ha := RotationTable.code_le r.2.2
    change (encodePair Nat.bits (encodePair Nat.bits enc) r).length≤_
    rw [encodePair_length,encodePair_length]
    change _≤_ at ha
    exact Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left _ hl) _)
      (Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left _ hr) _) ha)
  have h2 := EncodedList.length_bound enc s.2 _ he
  have h2' := h2.trans (Nat.mul_le_mul_right _ (show s.2.length≤N by omega))
  change (encodePair enc enc s).length≤_
  rw [encodePair_length]
  exact Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left _ h1) _) h2'
end MetricKMedian.PCP.Compiler.CSPTable

end Inline_PCPCSPTableBounds

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_AmplifierIteration
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAmplifierIteration
namespace MetricKMedian.PCP.Compiler.AmplifierProgram
open Amplifier Binary Binary.Automatic
open scoped Classical

noncomputable def fallback : CSPTable Label := ([()],[(0,0,Finset.univ)])
lemma fallback_valid : fallback.WellFormed := by
  constructor
  · exact Nat.zero_lt_one
  · intro r hr
    have hr' : r=(0,0,Finset.univ) := by simpa only [fallback,List.mem_singleton] using hr
    subst r
    exact ⟨Nat.zero_lt_one,Nat.zero_lt_one⟩
noncomputable def normalize (s : CSPTable Label) : CSPTable Label := if s.check then s else fallback
lemma normalize_valid (s : CSPTable Label) : (normalize s).WellFormed := by
  unfold normalize
  split_ifs with h
  · exact (CSPTable.check_iff s).mp h
  · exact fallback_valid
lemma poly_normalize : Poly normalize := by
  unfold normalize
  exact Poly.ite CSPTable.poly_check Poly.identity (Automatic.Poly.const _)
noncomputable def iterate : ℕ → CSPTable Label → CSPTable Label
  | 0, s => s
  | n+1, s => next (iterate n s)
end MetricKMedian.PCP.Compiler.AmplifierProgram

end Inline_PCPAmplifierIteration

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_AmplifierGuard
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAmplifierGuard
namespace MetricKMedian.PCP.Compiler.AmplifierProgram
open Amplifier Binary Binary.Automatic
open scoped Classical

abbrev State := ℕ × (ℕ × CSPTable Label)
noncomputable def guarded (s : State) : State :=
  (s.1,if s.2.1≤ s.1 then (2*s.2.1,next s.2.2) else s.2)
lemma poly_guarded : Poly guarded := by
  unfold guarded
  apply Poly.pair Poly.fst
  apply Poly.ite_prop
  · fun_prop
  · exact Poly.pair (by fun_prop) (poly_next.comp (Poly.snd.comp Poly.snd))
  · exact Poly.snd
noncomputable def schedule (s : CSPTable Label) (i : ℕ) : State :=
  (s.2.length,(2^(min i (Nat.log 2 s.2.length+1)),iterate (min i (Nat.log 2 s.2.length+1)) s))
lemma schedule_zero (s : CSPTable Label) : schedule s 0=(s.2.length,(1,s)) := by
  simp only [schedule,Nat.zero_min,pow_zero,iterate]
lemma schedule_succ (s : CSPTable Label) (h : s.WellFormed) (i : ℕ) :
    guarded (schedule s i)=schedule s (i+1) := by
  let n := Nat.log 2 s.2.length+1
  have guard (j : ℕ) : 2^j≤ s.2.length ↔ j<n :=
    (Nat.le_log_iff_pow_le (by omega : 1<2) (Nat.ne_of_gt h.1)).symm.trans Nat.lt_add_one_iff.symm
  by_cases hi : i<n
  · have h0 : min i n=i := min_eq_left hi.le
    have h1 : min (i+1) n=i+1 := min_eq_left hi
    have ht := (guard i).mpr hi
    change (s.2.length,if 2^(min i n)≤ s.2.length then _ else _)=_
    simp only [h0,ite_eq_left ht,schedule,show Nat.log 2 s.2.length+1=n from rfl,h1,iterate,pow_succ']
  · have h0 : min i n=n := min_eq_right (by omega)
    have h1 : min (i+1) n=n := min_eq_right (by omega)
    have ht : ¬2^n≤ s.2.length := by rw [guard]; exact lt_irrefl _
    change (s.2.length,if 2^(min i n)≤ s.2.length then _ else _)=_
    simp only [h0,ite_eq_right ht,schedule,show Nat.log 2 s.2.length+1=n from rfl,h1]
lemma guarded_iterate (s : CSPTable Label) (h : s.WellFormed) (i : ℕ) :
    guarded^[i] (s.2.length,(1,s))=schedule s i := by
  have hh := Expander.iterate_sequence guarded (schedule s) (schedule_succ s h) i
  rwa [schedule_zero] at hh
lemma schedule_counter (s : CSPTable Label) (h : s.WellFormed) (i : ℕ) :
    (schedule s i).2.1≤2*s.2.length := by
  change 2^(min i (Nat.log 2 s.2.length+1))≤_
  calc
    _ ≤ 2^(Nat.log 2 s.2.length+1) := Nat.pow_le_pow_right (by omega) (min_le_right _ _)
    _ = 2*2^(Nat.log 2 s.2.length) := pow_succ' _ _
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_log_le_self _ (Nat.ne_of_gt h.1))
noncomputable def generate (s : CSPTable Label) : CSPTable Label :=
  (guarded^[(normalize s).2.length+1] ((normalize s).2.length,(1,normalize s))).2.2
lemma generate_eq (s : CSPTable Label) :
    generate s=iterate (Nat.log 2 (normalize s).2.length+1) (normalize s) := by
  rw [generate,guarded_iterate _ (normalize_valid s)]
  change iterate (min _ _) _=_
  rw [min_eq_right]
  exact Nat.add_le_add_right (Nat.log_le_self 2 _) 1
end MetricKMedian.PCP.Compiler.AmplifierProgram

end Inline_PCPAmplifierGuard

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_AmplifierCompiler
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAmplifierCompiler
namespace MetricKMedian.PCP.Compiler.AmplifierProgram
open Amplifier Binary Binary.Automatic Polynomial
open scoped Classical

lemma normalize_count (s : CSPTable Label) :
    (normalize s).1.length+(normalize s).2.length≤(enc s).length+2 := by
  unfold normalize
  split_ifs
  · exact (CSPTable.count_le_encoding s).trans (by omega)
  · change 2≤_
    omega
lemma poly_initialState : Poly (fun s : CSPTable Label => ((normalize s).2.length,(1,normalize s))) :=
  Poly.pair (Poly.list_length.comp (Poly.snd.comp poly_normalize)) (Poly.pair (Automatic.Poly.const _) poly_normalize)
lemma poly_steps : Poly (fun s : CSPTable Label => (normalize s).2.length+2) := by
  exact Poly.nat_add.comp (Poly.pair (Poly.list_length.comp (Poly.snd.comp poly_normalize)) (Automatic.Poly.const _))
end MetricKMedian.PCP.Compiler.AmplifierProgram

end Inline_PCPAmplifierCompiler

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_InitialTable
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInitialTable
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic InitialAlphabet
open scoped Classical

namespace InitialProgram
variable (A : Type) [Fintype A] [DecidableEq A] [Nonempty A]
variable (s : CSPTable A) (h : s.WellFormed)
noncomputable def represents : (table A s).Represents (AlphabetReduction.paddedBinary
    ((bits A s).csp (bits_valid A s h))) := AlphabetProgram.represents A _ _
include h in
lemma valid : (table A s).WellFormed := by
  let : Nonempty (Fin (bits A s).2.length) := Fin.pos_iff_nonempty.mp (bits_valid A s h).1
  exact (represents A s h).wellFormed
end InitialProgram
end MetricKMedian.PCP.Compiler

end Inline_PCPInitialTable

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_LocalCompiler
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.functionHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPLocalCompiler
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

namespace LocalCompiler
variable {X VC TC Q A : Type} [Coding X] [Coding VC] [Coding TC]
  [Fintype Q] [Fintype A] [DecidableEq A] [DecidableEq VC] [DecidableEq TC]
  [Inhabited X] [Inhabited VC] [Inhabited TC] [Inhabited Q] [Inhabited A]
  [Coding Q] [Hardcoded Q]
omit [Inhabited Q] [Inhabited A] in
lemma poly_relation : Poly (fun p : Finset (Q→A) × Q => relation p.1 p.2) := hardcoded _
end LocalCompiler
end MetricKMedian.PCP.Compiler

end Inline_PCPLocalCompiler

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RepresentativeProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.prodHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.RationalRepresentatives.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Polynomial
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram

def Input.raw (x : Input) : Raw := ((List.ofFn x.R,(List.ofFn (fun i => List.ofFn (x.d i)),x.M)),setView x.U)
def Input.encode (x : Input) : List Bool := enc x.raw
def State.raw (s : State) : Raw × (Row × Row) := (s.input.raw,(setView s.cut.1,setView s.cut.2))
def State.encode (s : State) : List Bool := enc s.raw
end MetricKMedian.Preparation.RationalRepresentatives.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_BundleGeometryProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.RationalBundles.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram
def view {f n : ℕ} (d : Fin n → Fin n → ℚ) (di : Fin n → Fin f → ℚ)
    (F : Fin n → Finset (Fin f)) (y : Fin f → ℚ) : Raw :=
  ((List.ofFn (fun i => List.ofFn (d i)),List.ofFn (fun i => List.ofFn (di i))),
    (List.ofFn (fun i => setView (F i)),List.ofFn y))
 theorem neighborMask_view {n : ℕ} (ds : Fin n → ℚ) (t : Fin n) :
    neighborMask (List.ofFn ds,t.val)=setView (univ.erase t) := by
  simp only [neighborMask,indices,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,
    List.map_ofFn,Function.comp_def,setView,mem_erase,mem_univ,and_true]
  simp only [ne_eq,Fin.val_inj]
 theorem nextData_view {n : ℕ} (d : Fin n → Fin n → ℚ) (t : Fin n) :
     nextData (List.ofFn (d t),t.val)=(next d t).val := by
  unfold nextData
  rw [neighborMask_view,Completion.Rational.PackingProgram.any_view]
  simp only [decide_eq_true_eq]
  unfold next
  split_ifs with h
  · rw [MetricKMedian.MaskProgram.nearest_view]
  · rfl

 theorem bundleData_view {f n : ℕ} (d : Fin n → Fin n → ℚ) (di : Fin n → Fin f → ℚ)
    (F : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (δ : ℚ) (t : Fin n) :
    bundleData δ (view d di F y,t.val)=setView (bundle d di F δ t) := by
  simp only [bundleData,view,List.getElem?_ofFn,dite_eq_left t.isLt,Option.getD_some,Fin.eta,nextData_view]
  by_cases h : next d t=t
  · simp only [h,ite_true,bundle]
  · have hn : (next d t).val≠t.val := fun hh => h (Fin.ext hh)
    simp only [hn,ite_false,bundle,h,indices,List.length_ofFn,RoundingList.range_finRange,
      ← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,MetricKMedian.MaskProgram.get,List.getElem?_ofFn,
      dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,setView,mem_filter,Bool.decide_and]

 theorem bundlesData_view {f n : ℕ} (d : Fin n → Fin n → ℚ) (di : Fin n → Fin f → ℚ)
    (F : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (δ : ℚ) :
    bundlesData δ (view d di F y)=List.ofFn (fun t => setView (bundle d di F δ t)) := by
  unfold bundlesData
  simp only [view,indices,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn,Function.comp_def]
  change List.ofFn (fun t : Fin n => bundleData δ (view d di F y,t.val))=_
  simp only [bundleData_view]

 theorem missingData_view {f n : ℕ} (d : Fin n → Fin n → ℚ) (di : Fin n → Fin f → ℚ)
    (F : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (δ : ℚ) :
    missingData δ (view d di F y)=List.ofFn (fun t => setView (missing d di F δ t)) := by
  unfold missingData
  simp only [view,indices,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn,Function.comp_def]
  change List.ofFn (fun t : Fin n => List.ofFn (fun a : Fin f => MetricKMedian.MaskProgram.get ((List.ofFn (fun t => setView (F t)))[t.val]?.getD []) a.val && !MetricKMedian.MaskProgram.get (bundleData δ (view d di F y,t.val)) a.val))=_
  simp only [bundleData_view,MetricKMedian.MaskProgram.get,setView,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,
    Fin.eta,missing,mem_sdiff,Bool.decide_and,decide_not]

 theorem massData_view {f n : ℕ} (y : Fin f → ℚ) (P : Fin n → Finset (Fin f)) :
    massData (List.ofFn y,List.ofFn (fun t => setView (P t)))=List.ofFn (mass y P) := by
  simp only [massData,List.map_ofFn,Function.comp_def,indices,List.length_ofFn,RoundingList.range_finRange,
    ← List.ofFn_eq_map,List.map_ofFn,MetricKMedian.MaskProgram.get,setView,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),
    Option.getD_some,Fin.eta,decide_eq_true_eq,List.sum_ofFn,← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
  rfl
end MetricKMedian.Preparation.RationalBundles.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_LastFractionProgram
attribute [-simp] _root_.OAI.MetricKMedian.RationalSignedTerminal.point_state _root_.OAI.MetricKMedian.SparseTargetSubset.point_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.RoundingList.Last
open Binary Binary.Automatic Binary.Automatic.Poly Finset

 theorem first_list {n : ℕ} (p : Vector ℚ n) (h : (RationalWeightedStep.fractional p).Nonempty) :
    first p.toList=(RationalLastFraction.pick p h).val := by
  unfold first indices
  rw [Vector.length_toList]
  apply findIdx_min _ h
  intro i
  simp [frac,RationalWeightedStep.fractional,RationalWeightedStep.point]

end MetricKMedian.RoundingList.Last

end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Projection_RepairProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionRepairProgram
namespace MetricKMedian.PCP.Compiler.SeedProgram
open Binary Binary.Automatic RegularProgram CloudProgram
open scoped Classical

variable {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
noncomputable def legal (t : CSPTable A) (v : ℕ) (d : Port) : Finset (A×A) :=
  (allowed t v d).filter (fun a => (rotate t v d).1=v → a.1=a.2)
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPProjectionRepairProgram

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

 theorem boolState_list {n : ℕ} (u : Fin n → ℚ) (p : Vector ℚ n) (q : Fin n → Bool) :
    boolState ((List.ofFn u,p.toList),List.ofFn q)=(RationalSignedTerminal.state u p q).toList := by
  rw [point_toList]
  apply List.ext_getElem
  · simp only [boolState,List.length_map,List.length_range,List.length_ofFn,Vector.length_toList]
  · intro i hi hi'
    have hi'' : i<n := by simpa only [boolState,List.length_map,List.length_range,List.length_ofFn] using hi
    simp only [boolState,List.getElem_map,List.getElem_range,List.getElem?_ofFn,dite_eq_left hi'',Option.getD_some,
      RationalSignedTerminal.state,Vector.toList_ofFn,List.getElem_ofFn,SparseBernoulli.flag]

noncomputable def bernoulliInputProgram : PolyProgram Input.encode SparseBernoulli.Program.Input.encode bernoulliInput :=
  (snd erow erow).recode Input.raw (fun _ => rfl) (fun x => by
    change erow x.p.toList=erow (List.ofFn (RationalWeightedStep.point x.p))
    rw [point_toList])

end Terminal
end MetricKMedian.RoundingProgram
end

end OAI
end


