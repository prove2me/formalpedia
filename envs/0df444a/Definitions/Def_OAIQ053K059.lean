-- Prove2me | Definitions.Def_OAIQ053K059
-- name    : OAIQ053K059
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:10:35.51114+00:00
-- url     : https://prove2.me/theorems/04923269-04f2-461d-a1d8-dd7886b4e464
-- title:
--   Definitions bundle OAIQ053K059 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 26 declarations of OpenAI's Lean: 9 definitions, 3 instances and 14 theorems. The definitions and types are `OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.edgeRootEquiv`, `OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.represents`, `OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.vertexEquiv`, `OAI.MetricKMedian.PCP.Compiler.CSPTable.relationBound`, `OAI.MetricKMedian.PCP.Compiler.PowerProgram.Tag`, `OAI.MetricKMedian.PCP.Compiler.PowerProgram.edgeEquiv`, `OAI.MetricKMedian.PCP.Compiler.PowerProgram.rels`, `OAI.MetricKMedian.PCP.Compiler.PowerProgram.row`, `OAI.MetricKMedian.PCP.Compiler.PowerProgram.stop`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Amplification_PowerPrograms`, `KMedian_Amplification_PowerSpec`, `KMedian_Expanders_CloudPrograms`, `KMedian_Expanders_ExpanderGuard`, `KMedian_Machines_AlphabetSpec`, `KMedian_Machines_AlphabetTable`, `KMedian_Machines_BlendCompiler`, `KMedian_Machines_CSPTableBounds`, `KMedian_Machines_FiniteCoordinates`, `KMedian_Machines_GridTables`, `KMedian_Machines_LocalCompiler`, `KMedian_Machines_RawWalk`, `KMedian_Machines_RelabelTables`.
--
--   **Imports.** It imports the bundles `OAIQ053K052` and `OAIQ053K053` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K067` and `OAIQ053K068`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K052
import Definitions.Def_OAIQ053K053

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_FiniteCoordinates
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.relationCoding _root_.OAI.MetricKMedian.PCP.Compiler.relationHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFiniteCoordinates

namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

noncomputable instance functionHardcoded {I A : Type} [Fintype I] [Fintype A] : Hardcoded (I → A) :=
  ⟨fun _ _ _ f => finite_function f⟩
lemma poly_finCoordinates {X A : Type} [Coding X] [Fintype A] [Coding A] [Hardcoded A] [Inhabited A]
    (n : ℕ) (f : X → Fin n → A) (h : ∀ i, Poly (fun x => f x i)) : Poly f := by
  induction n with
  | zero =>
    apply poly_congr (Automatic.Poly.const (fun i : Fin 0 => Fin.elim0 i))
    intro x; funext i; exact Fin.elim0 i
  | succ n ih =>
    have ht := ih (fun x i => f x i.succ) (fun i => h i.succ)
    have hc : Poly (fun p : A × (Fin n → A) => Fin.cons p.1 p.2) := hardcoded _
    apply poly_congr (hc.comp (Poly.pair (h 0) ht))
    intro x; exact Fin.cons_self_tail (f x)
lemma poly_coordinates {X I A : Type} [Coding X] [Fintype I] [Fintype A]
    [Coding A] [Hardcoded A] [Inhabited A] (f : X → I → A)
    (h : ∀ i, Poly (fun x => f x i)) : Poly f := by
  have hf := poly_finCoordinates (Fintype.card I)
    (fun x i => f x ((Fintype.equivFin I).symm i)) (fun i => h _)
  have hc : Poly (fun g : Fin (Fintype.card I) → A => fun i => g (Fintype.equivFin I i)) := hardcoded _
  apply poly_congr (hc.comp hf)
  intro x; funext i; exact congrArg (f x) ((Fintype.equivFin I).symm_apply_apply i)
end MetricKMedian.PCP.Compiler

end Inline_PCPFiniteCoordinates

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_RawWalk
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.relationCoding _root_.OAI.MetricKMedian.PCP.Compiler.relationHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
lemma poly_at (cap n : ℕ) : Poly (fun p : (T × ℕ) × (Fin cap → D) => vertexAt rotate cap p.1.1 p.1.2 p.2 n) := by
  induction n with
  | zero => exact Poly.snd.comp Poly.fst
  | succ n ih =>
    have hc : Poly (fun w : Fin cap → D => port cap w n) := hardcoded _
    exact Poly.fst.comp (hp.comp (Poly.pair (Poly.pair (Poly.fst.comp Poly.fst) ih) (hc.comp Poly.snd)))
lemma poly_backs (cap : ℕ) : Poly (fun p : (T × ℕ) × (Fin cap → D) => backs rotate cap p.1.1 p.1.2 p.2) := by
  apply poly_coordinates
  intro i
  have hc : Poly (fun w : Fin cap → D => w i) := hardcoded _
  exact Poly.snd.comp (hp.comp (Poly.pair (Poly.pair (Poly.fst.comp Poly.fst) (poly_at rotate hp cap i.val))
    (hc.comp Poly.snd)))
end MetricKMedian.PCP.Compiler.RawWalk

end Inline_PCPRawWalk

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PowerPrograms
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
abbrev Tag (t cap : ℕ) := (Fin cap → Fin (t+1)) × (Fin cap → D)
noncomputable def stop (t cap : ℕ) (c : Fin cap → Fin (t+1)) : Fin (cap+1) :=
  ⟨Stopped.length t cap c, by have := Stopped.length_le t cap c; omega⟩
def rels (cap : ℕ) (s : T) (v : ℕ) (w : Fin cap → D) : Fin cap → Finset (A × A) :=
  fun i => allow s (RawWalk.vertexAt rot cap s v w i.val) (w i)
include hr ha in
omit [Hardcoded D] [DecidableEq A] [Inhabited A] in
lemma poly_rels (cap : ℕ) : Poly (fun p : (T × ℕ) × (Fin cap → D) => rels rot allow cap p.1.1 p.1.2 p.2) := by
  apply poly_coordinates
  intro i
  have hc : Poly (fun w : Fin cap → D => w i) := hardcoded _
  exact ha.comp (Poly.pair (Poly.pair (Poly.fst.comp Poly.fst) (RawWalk.poly_at rot hr cap i.val)) (hc.comp Poly.snd))
noncomputable def row (t cap : ℕ) (s:T) (v:ℕ) (tag:Tag (D := D) t cap) : CSPRow (Advice D A cap) :=
  (v,RawWalk.vertexAt rot cap s v tag.2 (stop t cap tag.1).val,
    relation cap (stop t cap tag.1) tag.2 (RawWalk.backs rot cap s v tag.2) (rels rot allow cap s v tag.2))
end MetricKMedian.PCP.Compiler.PowerProgram

end Inline_PCPPowerPrograms

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PowerSpec
attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.activeNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPowerSpec
namespace MetricKMedian.PCP.Compiler.PowerProgram
open Binary Binary.Automatic
open scoped Classical

variable {V D A T : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
  [Inhabited D] [Fintype A] [Inhabited A] [DecidableEq A] [Coding T] [Coding D] [Hardcoded D]
variable {G : PortGraph V D} (C : PortCSP G A)
def edgeEquiv (t cap : ℕ) : V × Tag (D := D) t cap ≃ PortCSP.PowerEdge (G := G) t cap where
  toFun z := (z.2.1,PortGraph.Walk.ofWord z.1 z.2.2)
  invFun z := (z.2.vertex 0,(z.1,z.2.port))
  left_inv z := by simp only [PortGraph.Walk.ofWord,PortGraph.trace_zero]
  right_inv z := by
    apply Prod.ext
    · rfl
    · exact PortGraph.Walk.wordEquiv.symm_apply_apply z.2
variable (rot : T → ℕ → D → ℕ × D) (allow : T → ℕ → D → Finset (A × A))
  (code : V → ℕ) (s : T)
omit [Fintype V] [Nonempty V] [Nonempty D] [DecidableEq A] [Coding T] [Coding D]
  [Hardcoded D] in
lemma row_correct (hr : ∀ v d, rot s (code v) d=(code (G.step v d),G.back v d))
    (ha : ∀ v d, allow s (code v) d=C.allowed (v,d))
    (t cap : ℕ) (z : PortCSP.PowerEdge (G := G) t cap) :
    row rot allow t cap s (code (z.2.vertex 0)) (z.1,z.2.port)=
      (code ((C.powered (cap := cap) t).left z),code ((C.powered (cap := cap) t).right z),
        (C.powered (cap := cap) t).allowed z) := by
  unfold row
  rw [RawWalk.at_correct rot G code s hr]
  · have hb : RawWalk.backs rot cap s (code (z.2.vertex 0)) z.2.port=
        fun i => G.back (z.2.vertex i.castSucc) (z.2.port i) := by
      funext i
      exact RawWalk.backs_correct rot G code s hr cap z.2 i
    have hl : rels rot allow cap s (code (z.2.vertex 0)) z.2.port=
        fun i => C.allowed (z.2.vertex i.castSucc,z.2.port i) := by
      funext i
      unfold rels
      rw [RawWalk.at_correct rot G code s hr cap z.2 i.val (Nat.le_of_lt i.isLt),ha]
      rfl
    rw [hb,hl,relation_correct C cap z.2 (stop t cap z.1)]
    simp only [PortCSP.powered,PortCSP.stoppedPath,stop,PortGraph.Walk.segment,Nat.zero_add,Fin.val_zero,Fin.val_last]
    rfl
  · exact Nat.le_of_lt_succ (stop t cap z.1).isLt
end MetricKMedian.PCP.Compiler.PowerProgram

end Inline_PCPPowerSpec

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_ExpanderGuard
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPExpanderGuard
namespace MetricKMedian.PCP.Compiler.Expander
open ExpanderFamily RotationTable Binary Binary.Automatic
open scoped Classical

lemma generate_table (xs : List Unit) : generate xs=table (graph (level xs.length)) (vertexEquiv (level xs.length)) := by
  unfold generate
  rw [iterate_guarded]
  dsimp only [sequence]
  rw [min_eq_right (level_le xs.length)]
  exact Eq.refl _
end MetricKMedian.PCP.Compiler.Expander

end Inline_PCPExpanderGuard

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_CloudPrograms
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.functionHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCloudPrograms
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

noncomputable instance unitHardcoded : Hardcoded Unit where
  all B _ _ f := poly_congr (Automatic.Poly.const (f ())) (fun u => by cases u; rfl)
end MetricKMedian.PCP.Compiler

end Inline_PCPCloudPrograms

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_GridTables
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPGridTables
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

namespace CSPTable
variable {A T B : Type} [Fintype A] [Coding T] [Coding B]
lemma poly_grid [Inhabited B] (seeds : T → List Unit) (tags : List B) (row : T → ℕ → B → CSPRow A)
    (hs : Poly seeds) (hr : Poly (fun p : (T × ℕ) × B => row p.1.1 p.1.2 p.2)) :
    Poly (fun t => grid (seeds t) tags (row t)) := by
  unfold grid
  apply Poly.pair hs
  apply Poly.list_flatMap
  · apply Poly.list_map hr (Automatic.Poly.const tags)
  · exact Poly.list_indices.comp hs
end CSPTable
end MetricKMedian.PCP.Compiler

end Inline_PCPGridTables

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_AlphabetTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAlphabetTable
namespace MetricKMedian.PCP.Compiler.AlphabetProgram
open AlphabetReduction Binary Binary.Automatic
open scoped Classical

variable (K : Type) [Fintype K] [DecidableEq K]
noncomputable def vertexEquiv (s : CSPTable (BitVector K)) :
    PaddedNode (Fin s.1.length) (Fin s.2.length) K ≃ Fin (seeds K s).length :=
  (nodeEquiv K _ _).trans (finCongr (seeds_length K s).symm)
noncomputable def edgeRootEquiv (s : CSPTable (BitVector K)) : Fin s.2.length ≃ Fin (roots K s).length :=
  finCongr (List.length_map _).symm
omit [Fintype K] [DecidableEq K] in
lemma row_get (s : CSPTable (BitVector K)) (e : Fin s.2.length) : CSPTable.row s e.val=s.2[e.val] := by
  simp only [CSPTable.row,List.getElem?_eq_getElem e.isLt,Option.getD_some]
end MetricKMedian.PCP.Compiler.AlphabetProgram

end Inline_PCPAlphabetTable

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_AlphabetSpec
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.activeNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAlphabetSpec
namespace MetricKMedian.PCP.Compiler.AlphabetProgram
open AlphabetReduction Binary Binary.Automatic
open scoped Classical

variable (K : Type) [Fintype K] [DecidableEq K]
lemma position_correct (nv ne : ℕ) (C : BinaryCSP (Fin nv) (Fin ne) (BitVector K))
    (e : Fin ne) (a : LocalRelation.LocalPosition (C.allowed e : LocalRelation.Relation K)) :
    endpoint K nv e.val ((C.left e).val,(C.right e).val,C.allowed e)
      (positionInfo K (C.allowed e) a)=
    (nodeEquiv K nv ne (.inl (positionEmbed C (localMap C e a)))).val := by
  rcases a with x | (x | ⟨b,x⟩)
  · change (if (2:Fin 3)=0 then _ else if (2:Fin 3)=1 then _ else _)=_
    simp only [show (2:Fin 3)≠0 from by decide,show (2:Fin 3)≠1 from by decide,ite_false]
    rfl
  · change (if (2:Fin 3)=0 then _ else if (2:Fin 3)=1 then _ else _)=_
    simp only [show (2:Fin 3)≠0 from by decide,show (2:Fin 3)≠1 from by decide,ite_false]
    rfl
  · by_cases hb:b=0
    · simp only [positionInfo,hb,ite_eq_left,endpoint]
      change _=bitIndex K x+B K*(if (0:Fin 2)=0 then C.left e else C.right e).val
      simp only [ite_true]
    · simp only [positionInfo,hb,ite_false,endpoint]
      simp only [show (1:Fin 3)≠0 from by decide,ite_false,ite_eq_left]
      change _=bitIndex K x+B K*(if b=0 then C.left e else C.right e).val
      simp only [ite_eq_right hb]
variable (s : CSPTable (BitVector K)) (h : s.WellFormed)
lemma row_correct (e : Fin s.2.length) (z : Tag K) :
    row K s e.val z=
      ((vertexEquiv K s ((paddedBinary (s.csp h)).left ((e,z.1),z.2))).val,
       (vertexEquiv K s ((paddedBinary (s.csp h)).right ((e,z.1),z.2))).val,
       (paddedBinary (s.csp h)).allowed ((e,z.1),z.2)) := by
  unfold row
  rw [row_get]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · have hp := position_correct K s.1.length s.2.length (s.csp h) e
        ((LocalRelation.query ((s.csp h).allowed e : LocalRelation.Relation K) z.1.1
          (z.1.2 ((s.csp h).allowed e) z.1.1)).address z.2)
      exact hp
    · rfl
noncomputable def represents : (table K s).Represents (paddedBinary (s.csp h)) := by
  have he := CSPTable.rect_build (paddedBinary (s.csp h)) (seeds K s) (roots K s)
    (vertexEquiv K s) (edgeRootEquiv K s) (Ordered.fixed (Tag K))
    (Equiv.prodAssoc _ _ _).symm (row K s) (by
      intro e z
      exact row_correct K s h e z)
  unfold table
  rw [he]
  exact CSPTable.build_represents _ _ _
end MetricKMedian.PCP.Compiler.AlphabetProgram

end Inline_PCPAlphabetSpec

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_BlendCompiler
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.relationCoding _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPBlendCompiler
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic

variable {X D S : Type} [Coding X] [Coding D] [Coding S]
lemma poly_blendProgram (f : X → D → ℕ × D) (g : X → S → ℕ × S)
    (hf : Poly (fun p : X × D => f p.1 p.2))
    (hg : Poly (fun p : X × S => g p.1 p.2)) :
    Poly (fun p : X × (Fin 3 × D × S) => blendProgram f g p.1 p.2) := by
  unfold blendProgram
  dsimp only
  apply Poly.ite_prop
  · exact (hardcoded (fun i : Fin 3 => decide (i=0))).comp (Poly.fst.comp Poly.snd)
  · have hp : Poly (fun x : X × (Fin 3 × D × S) => f x.1 x.2.2.1) :=
      hf.comp (Poly.pair Poly.fst (Poly.fst.comp (Poly.snd.comp Poly.snd)))
    exact Poly.pair (Poly.fst.comp hp) (Poly.pair (Poly.fst.comp Poly.snd)
      (Poly.pair (Poly.snd.comp hp) (Poly.snd.comp (Poly.snd.comp Poly.snd))))
  · have hp : Poly (fun x : X × (Fin 3 × D × S) => g x.1 x.2.2.2) :=
      hg.comp (Poly.pair Poly.fst (Poly.snd.comp (Poly.snd.comp Poly.snd)))
    exact Poly.pair (Poly.fst.comp hp) (Poly.pair (Poly.fst.comp Poly.snd)
      (Poly.pair (Poly.fst.comp (Poly.snd.comp Poly.snd)) (Poly.snd.comp hp)))
end MetricKMedian.PCP.Compiler

end Inline_PCPBlendCompiler

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
noncomputable def relationBound : ℕ := RotationTable.codeBound (D := Finset (A × A))
omit [DecidableEq A] in
lemma count_le_encoding (s : CSPTable A) : s.1.length+s.2.length≤(enc s).length := by
  have h1 := EncodedList.length_le enc s.1
  have h2 := EncodedList.length_le enc s.2
  change s.1.length ≤ (enc s.1).length at h1
  change s.2.length ≤ (enc s.2).length at h2
  change _≤(encodePair enc enc s).length
  rw [encodePair_length]
  omega
end MetricKMedian.PCP.Compiler.CSPTable

end Inline_PCPCSPTableBounds

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_LocalCompiler
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.functionHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
noncomputable instance assignmentSetHardcoded : Hardcoded (Finset (Q→A)) := ⟨fun _ _ _ f => finite_function f⟩
end LocalCompiler
end MetricKMedian.PCP.Compiler

end Inline_PCPLocalCompiler

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_RelabelTables
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.unitHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRelabelTables
namespace MetricKMedian.PCP.Compiler.CSPTable
open Binary Binary.Automatic
open scoped Classical

variable {A B V E : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  [Fintype V] [Fintype E]
omit [DecidableEq A] [DecidableEq B] in
lemma poly_relabel (e : A ≃ B) : Poly (relabel e) := by
  have hh : Poly (fun R : Finset (A × A) => R.map (e.prodCongr e).toEmbedding) := hardcoded _
  unfold relabel
  apply Poly.pair Poly.fst
  apply Poly.list_map _ Poly.snd
  exact Poly.pair (Poly.fst.comp Poly.snd)
    (Poly.pair (Poly.fst.comp (Poly.snd.comp Poly.snd))
      (hh.comp (Poly.snd.comp (Poly.snd.comp Poly.snd))))
end MetricKMedian.PCP.Compiler.CSPTable

end Inline_PCPRelabelTables

end OAI
end


