-- Prove2me | Definitions.Def_OAIQ053K052
-- name    : OAIQ053K052
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:09:15.850989+00:00
-- url     : https://prove2.me/theorems/89b9344e-285f-4141-b9f9-b6aad491d4f1
-- title:
--   Definitions bundle OAIQ053K052 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 81 declarations of OpenAI's Lean: 29 definitions, 1 inductive type or structure, 8 instances and 43 theorems. The definitions and types are `OAI.MetricKMedian.LPBinary.Repair.assignmentProgram`, `OAI.MetricKMedian.LPBinary.Repair.assignmentsProgram`, `OAI.MetricKMedian.LPBinary.Repair.dominatedProgram`, `OAI.MetricKMedian.LPBinary.Repair.dotProgram`, `OAI.MetricKMedian.LPBinary.Repair.valueProgram`, `OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.endpoint`, `OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.roots`, `OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.row`, `OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.seeds`, `OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.table`, `OAI.MetricKMedian.PCP.Compiler.CloudProgram.cloud`, `OAI.MetricKMedian.PCP.Compiler.CloudProgram.global`, `OAI.MetricKMedian.PCP.Compiler.CloudProgram.index`, `OAI.MetricKMedian.PCP.Compiler.CloudProgram.nodes`, `OAI.MetricKMedian.PCP.Compiler.Expander.State`, `OAI.MetricKMedian.PCP.Compiler.Expander.family`, `OAI.MetricKMedian.PCP.Compiler.Expander.generate`, `OAI.MetricKMedian.PCP.Compiler.Expander.guarded`, `OAI.MetricKMedian.PCP.Compiler.Expander.initial`, `OAI.MetricKMedian.PCP.Compiler.Expander.sequence`, `OAI.MetricKMedian.PCP.Compiler.Expander.sizePoly`, `OAI.MetricKMedian.PCP.Compiler.Hardcoded`, `OAI.MetricKMedian.PCP.Compiler.RotationTable.codeBound`, `OAI.MetricKMedian.PCP.Compiler.RotationTable.sizeBound`, `OAI.MetricKMedian.PCP.Compiler.finiteIndexProgram`, `OAI.MetricKMedian.RoundingProgram.SignedRound.boundState`, `OAI.MetricKMedian.RoundingProgram.SignedRound.partialInput`, `OAI.MetricKMedian.RoundingProgram.SignedRound.partialInputs`, `OAI.MetricKMedian.RoundingProgram.SignedRound.result`, `OAI.MetricKMedian.SparseCounts.Program.State.step`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Expanders_CloudPrograms`, `KMedian_Expanders_ExpanderCompiler`, `KMedian_Expanders_ExpanderGuard`, `KMedian_Expanders_ExpanderStep`, `KMedian_Expanders_ExpanderTables`, `KMedian_Machines_AlphabetIndex`, `KMedian_Machines_AlphabetTable`, `KMedian_Machines_FiniteCompiler`, `KMedian_Machines_Hardcoded`, `KMedian_Machines_RawCSP`, `KMedian_Machines_RawRotation`, `KMedian_Machines_RectTables`, `KMedian_Machines_RotationBounds`, `KMedian_Optimization_ApproximationListProgram`, `KMedian_Optimization_FractionalListChecks`, `KMedian_Process_CountStepProgram`, `KMedian_Rounding_SignedRoundProgram`.
--
--   **Imports.** It imports the bundles `OAIQ053K044`, `OAIQ053K045`, `OAIQ053K046` and `OAIQ053K047` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K058`, `OAIQ053K059` and `OAIQ053K060`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K044
import Definitions.Def_OAIQ053K045
import Definitions.Def_OAIQ053K046
import Definitions.Def_OAIQ053K047

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_FiniteCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFiniteCompiler

namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

noncomputable def finiteIndexProgram (A : Type) [Fintype A] :
    PolyProgram (finiteCoding A).encode Nat.bits (fun a => (Fintype.equivFin A a).val) where
  machine := (PolyProgram.identity Nat.bits).machine
  time := (PolyProgram.identity Nat.bits).time
  outputs a := (PolyProgram.identity Nat.bits).outputs (Fintype.equivFin A a).val
lemma finite_function {A B : Type} [Fintype A] [Coding B] [Inhabited B] (f : A → B) :
    @Poly A B (finiteCoding A) _ f := by
  let table := List.ofFn (fun i => f ((Fintype.equivFin A).symm i))
  let P := ((PolyProgram.constant (finiteCoding A).encode (Binary.encodeList enc) table).fanout
    (finiteIndexProgram A)).comp (PolyProgram.listGetD enc (default : B))
  refine ⟨P.congr f ?_⟩
  intro a
  simp only [Function.comp_def,table,List.getElem?_ofFn,Fin.isLt,↓reduceDIte,
    Option.getD_some,Fin.eta,Equiv.symm_apply_apply]
end MetricKMedian.PCP.Compiler

end Inline_PCPFiniteCompiler

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_Hardcoded
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPHardcoded
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

class Hardcoded (A : Type) [Coding A] : Prop where
  all : ∀ (B : Type) [Coding B] [Inhabited B] (f : A → B), Poly f
lemma hardcoded {A B : Type} [Coding A] [Hardcoded A] [Coding B] [Inhabited B]
    (f : A → B) : Poly f := Hardcoded.all B f
noncomputable instance finCoding (n : ℕ) : Coding (Fin n) := finiteCoding _
noncomputable instance finHardcoded (n : ℕ) : Hardcoded (Fin n) := ⟨fun _ _ _ f => finite_function f⟩
noncomputable instance prodHardcoded {A B : Type} [Coding A] [Coding B]
    [Hardcoded A] [Hardcoded B] [Fintype B] : Hardcoded (A × B) where
  all C _ _ f := by
    let table : A → List C := fun a => List.ofFn (fun i => f (a,(Fintype.equivFin B).symm i))
    have ht : Poly table := hardcoded _
    have hi : Poly (fun b : B => (Fintype.equivFin B b).val) := hardcoded _
    have hp : Poly (fun p : A × B => (table p.1)[(Fintype.equivFin B p.2).val]?.getD default) :=
      Poly.list_getD_comp default (ht.comp Poly.fst) (hi.comp Poly.snd)
    apply poly_congr hp
    intro p
    simp only [table,List.getElem?_ofFn,Fin.isLt,↓reduceDIte,Option.getD_some,Fin.eta,Equiv.symm_apply_apply]
end MetricKMedian.PCP.Compiler

end Inline_PCPHardcoded

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_RawRotation
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRawRotation

namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

namespace RotationTable
variable {D : Type} [Fintype D] [Inhabited D]
variable [Coding D] [Hardcoded D]
lemma poly_lookup : Poly (fun s : RotationTable D × (ℕ × D) => lookup s.1 s.2.1 s.2.2) := by
  unfold lookup
  apply Poly.list_getD_comp
  · exact Poly.list_getD_comp [] Poly.fst (Poly.fst.comp Poly.snd)
  · exact (hardcoded (fun d : D => (Fintype.equivFin D d).val)).comp (Poly.snd.comp Poly.snd)
end RotationTable
end MetricKMedian.PCP.Compiler

end Inline_PCPRawRotation

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_ExpanderStep
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.PortCSP.badDecidable _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPExpanderStep

namespace MetricKMedian.PCP.Compiler.Expander
open Binary Binary.Automatic ExpanderFamily RotationTable
open scoped Classical

@[fun_prop] lemma poly_baseRotate : Poly (fun p : Branch × SmallPort => base.rotate p) := hardcoded _
@[fun_prop] lemma poly_nodeIndex : Poly (fun p : ℕ × Branch => nodeIndex p.1 p.2) := by
  unfold nodeIndex
  have h : Poly (fun b : Branch => (Fintype.equivFin Branch b).val) := hardcoded _
  exact Automatic.Poly.nat_add.comp (Automatic.Poly.pair
    (Automatic.Poly.nat_mul.comp (Automatic.Poly.pair Automatic.Poly.fst (Automatic.Poly.const growth)))
    (h.comp Automatic.Poly.snd))
@[fun_prop] lemma poly_rotate : Poly (fun p : Raw × (ℕ × (Branch × Degree)) => rotate p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold rotate
  have hl := poly_lookup (D := Degree)
  fun_prop
lemma poly_rotate4 : Poly (fun p : ((Raw × ℕ) × Branch) × Degree =>
    rotate p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  unfold rotate
  have hl := poly_lookup (D := Degree)
  fun_prop
lemma poly_next : Poly next := by
  unfold next
  apply Poly.list_flatMap
  · apply Poly.list_map
    · apply Poly.list_map
      · exact poly_rotate4
      · exact Automatic.Poly.const _
    · exact Automatic.Poly.const _
  · exact Poly.list_indices
lemma next_length (R : Raw) : (next R).length=R.length*Fintype.card Branch := by
  unfold next
  rw [length_flatMap_uniform _ _ (Fintype.card Branch) (by intro v hv; simp only [List.length_map,ports_length]),List.length_range]
lemma lookup_next (R : Raw) (v : ℕ) (hv : v<R.length) (b : Branch) (d : Degree) :
    lookup (next R) (nodeIndex v b) d=rotate R v b d := by
  change lookup (blockRows R.length (rotate R)) (nodeIndex v b) d=rotate R v b d
  have h := lookup_blockRows R.length (rotate R) v hv b d
  simpa only [nodeIndex,card_branch] using h
lemma rotate_table_aux {V : Type} {N : ℕ} (G : PortGraph V Degree) (e : V ≃ Fin N)
    (v : V) (b : Branch) (d : Degree) :
    rotate (table G e) (e v).val b d =
    let h1 := base.rotate (b,d.1)
    let u := G.step v h1.1.1
    let w := G.step u h1.1.2
    let h2 := base.rotate ((G.back u h1.1.2,G.back v h1.1.1),d.2)
    (nodeIndex (e w).val h2.1,(h2.2,h1.2)) := by
  simp only [rotate,lookup_table]
lemma graph_rotate_succ (n : ℕ) (v : Vertex n) (b : Branch) (d : Degree) :
    (graph (n+1)).rotate ((v,b),d)=
    let h1 := base.rotate (b,d.1)
    let u := (graph n).step v h1.1.1
    let w := (graph n).step u h1.1.2
    let h2 := base.rotate (((graph n).back u h1.1.2,(graph n).back v h1.1.1),d.2)
    ((w,h2.1),(h2.2,h1.2)) := rfl
lemma rotate_table (n : ℕ) (v : Vertex n) (b : Branch) (d : Degree) :
    rotate (table (graph n) (vertexEquiv n)) (vertexEquiv n v).val b d=
      ((vertexEquiv (n+1) ((graph (n+1)).step (v,b) d)).val,(graph (n+1)).back (v,b) d) := by
  have h := rotate_table_aux (graph n) (vertexEquiv n) v b d
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  change ((vertexEquiv (n+1) ((graph (n+1)).rotate ((v,b),d)).1).val,
    ((graph (n+1)).rotate ((v,b),d)).2)=_
  simp only [graph_rotate_succ,vertexEquiv_succ,card_branch,nodeIndex]
end MetricKMedian.PCP.Compiler.Expander

end Inline_PCPExpanderStep

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_RotationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRotationBounds
namespace MetricKMedian.PCP.Compiler.RotationTable
open Binary Binary.Automatic Finset
open scoped BigOperators Classical

variable {D : Type} [Fintype D] [Inhabited D]
omit [Inhabited D]
variable [Coding D]
noncomputable def codeBound : ℕ := ∑ d : D, (enc d).length
lemma code_le (d : D) : (enc d).length ≤ codeBound (D := D) := by
  unfold codeBound
  exact single_le_sum (f := fun d : D => (enc d).length) (fun _ _ => Nat.zero_le _) (mem_univ d)
noncomputable def sizeBound (N : ℕ) : ℕ :=
  N*(2*(Fintype.card D*(2*(2*(N+1)+1+codeBound (D := D))+1))+1)
end MetricKMedian.PCP.Compiler.RotationTable

end Inline_PCPRotationBounds

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_ExpanderTables
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPExpanderTables
namespace MetricKMedian.PCP.Compiler.Expander
open ExpanderFamily RotationTable
open scoped Classical

lemma next_table (n : ℕ) :
    next (table (graph n) (vertexEquiv n))=table (graph (n+1)) (vertexEquiv (n+1)) := by
  apply ext_lookup
  · simp only [next_length,table_length,pow_succ]
  · exact blockRows_row_length _ _
  · intro row hr
    exact (table_wellFormed _ _ row hr).1
  · intro i hi d
    have hi' : i < (Fintype.card Branch)^(n+1) := by
      simpa only [next_length,table_length,pow_succ] using hi
    let w := (vertexEquiv (n+1)).symm ⟨i,hi'⟩
    have hw : (vertexEquiv (n+1) w).val=i := by
      simp only [w,Equiv.apply_symm_apply]
    obtain ⟨v,b⟩ := w
    have hj : i=nodeIndex (vertexEquiv n v).val b := by
      exact hw.symm.trans (by simpa only [nodeIndex,card_branch] using vertexEquiv_succ n v b)
    calc
      lookup (next (table (graph n) (vertexEquiv n))) i d =
          rotate (table (graph n) (vertexEquiv n)) (vertexEquiv n v).val b d := by
        rw [hj]
        exact lookup_next _ _ (by rw [table_length]; exact (vertexEquiv n v).isLt) _ _
      _ = ((vertexEquiv (n+1) ((graph (n+1)).step (v,b) d)).val,(graph (n+1)).back (v,b) d) :=
        rotate_table n v b d
      _ = lookup (table (graph (n+1)) (vertexEquiv (n+1))) (vertexEquiv (n+1) (v,b)).val d :=
        (lookup_table _ _ _ _).symm
      _ = lookup (table (graph (n+1)) (vertexEquiv (n+1))) i d := by rw [hw]
noncomputable def initial : Raw := table (graph 0) (vertexEquiv 0)
end MetricKMedian.PCP.Compiler.Expander

end Inline_PCPExpanderTables

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

abbrev State := ℕ × Raw
noncomputable def guarded (s : State) : State :=
  (s.1, if s.2.length ≤ s.1 + 1 then next s.2 else s.2)
lemma poly_guarded : Poly guarded := by
  unfold guarded
  apply Poly.pair Poly.fst
  apply Poly.ite_prop
  · fun_prop
  · exact poly_next.comp Poly.snd
  · exact Poly.snd
noncomputable def family (n : ℕ) : Raw := table (graph n) (vertexEquiv n)
lemma family_zero : family 0=initial := Eq.refl _
lemma next_family (n : ℕ) : next (family n)=family (n+1) := next_table n
lemma family_length (n : ℕ) : (family n).length=growth^n := by
  exact (table_length (graph n) (vertexEquiv n)).trans (congrArg (fun k:ℕ => k^n) card_branch)
lemma family_wellFormed (n : ℕ) : WellFormed (family n) := by
  rw [family]
  exact table_wellFormed _ _
lemma guard_at (n i : ℕ) : (family i).length ≤ n+1 ↔ i<level n := by
  rw [family_length,level]
  exact (Nat.le_log_iff_pow_le growth_gt_one (Nat.succ_ne_zero n)).symm.trans Nat.lt_add_one_iff.symm
noncomputable def sequence (n i : ℕ) : State :=
  (n,family (min i (level n)))
lemma sequence_zero (n : ℕ) : sequence n 0=(n,initial) := by
  simp only [sequence,Nat.zero_min,family_zero]
lemma sequence_succ (n i : ℕ) : guarded (sequence n i)=sequence n (i+1) := by
  by_cases hi : i<level n
  · have h0 : min i (level n)=i := min_eq_left hi.le
    have h1 : min (i+1) (level n)=i+1 := min_eq_left hi
    have ht := (guard_at n i).mpr hi
    simp only [sequence,h0,h1,guarded,ite_eq_left ht,next_family]
  · have h0 : min i (level n)=level n := min_eq_right (by omega)
    have h1 : min (i+1) (level n)=level n := min_eq_right (by omega)
    have ht : ¬(family (level n)).length ≤ n+1 := by
      rw [guard_at]; exact lt_irrefl _
    simp only [sequence,h0,h1,guarded,ite_eq_right ht]
lemma iterate_guarded (n i : ℕ) : guarded^[i] (n,initial)=sequence n i := by
  have h := iterate_sequence guarded (sequence n) (sequence_succ n) i
  rwa [sequence_zero] at h
lemma sequence_wellFormed (n i : ℕ) : WellFormed (sequence n i).2 := by
  dsimp only [sequence]
  exact family_wellFormed (min i (level n))
lemma sequence_length (n i : ℕ) : (sequence n i).2.length ≤ growth*(n+1) := by
  dsimp only [sequence]
  rw [family_length]
  apply (Nat.pow_le_pow_right (by have := growth_gt_one; omega) (min_le_right i (level n))).trans
  simpa only [card_vertex] using padding_upper n
noncomputable def generate (xs : List Unit) : Raw := (guarded^[xs.length+1] (xs.length,initial)).2
end MetricKMedian.PCP.Compiler.Expander

end Inline_PCPExpanderGuard

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_ExpanderCompiler
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPExpanderCompiler
namespace MetricKMedian.PCP.Compiler.Expander
open ExpanderFamily RotationTable Binary Binary.Automatic Polynomial
open scoped Classical

noncomputable def sizePoly : Polynomial ℕ :=
  2*(X+1)+1+(C growth*(X+1)) *
    (2*(C (Fintype.card Degree)*(2*(2*(C growth*(X+1)+1)+1+C (codeBound (D := Degree)))+1))+1)
lemma poly_initialState : Poly (fun xs : List Unit => (xs.length,initial)) :=
  Poly.pair Poly.list_length (Automatic.Poly.const _)
lemma poly_steps : Poly (fun xs : List Unit => xs.length+2) := by fun_prop
end MetricKMedian.PCP.Compiler.Expander

end Inline_PCPExpanderCompiler

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_RawCSP
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRawCSP
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

noncomputable instance relationCoding (A : Type) [Fintype A] : Coding (Finset (A × A)) := finiteCoding _
noncomputable instance relationHardcoded (A : Type) [Fintype A] : Hardcoded (Finset (A × A)) :=
  ⟨fun _ _ _ f => finite_function f⟩
namespace CSPTable
variable {A : Type} [Fintype A] [DecidableEq A]
variable {V E : Type} [Fintype V] [Fintype E]
omit [DecidableEq A] in
lemma poly_row : Poly (fun p : CSPTable A × ℕ => row p.1 p.2) := by
  unfold row
  fun_prop
end CSPTable
end MetricKMedian.PCP.Compiler

end Inline_PCPRawCSP

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_CloudPrograms
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCloudPrograms
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

noncomputable instance boolHardcoded : Hardcoded Bool where
  all B _ _ f := poly_congr (Poly.ite Poly.identity (Automatic.Poly.const (f true)) (Automatic.Poly.const (f false)))
    (fun u => by cases u <;> rfl)
namespace CloudProgram
variable {A : Type} [Fintype A]
noncomputable def cloud (t : CSPTable A) (v : ℕ) : Expander.Raw :=
  Expander.generate ((incident t v).tail.map (fun _ => ()))
noncomputable def nodes (t : CSPTable A) : List (ℕ × ℕ) :=
  (active t).flatMap (fun v => (List.range (cloud t v).length).map (fun j => (v,j)))
noncomputable def global (t : CSPTable A) : Expander.Raw :=
  Expander.generate ((nodes t).tail.map (fun _ => ()))
noncomputable def index (t : CSPTable A) (p : ℕ × ℕ) : ℕ :=
  (nodes t).findIdx (fun q => decide (q.1=p.1 ∧ q.2=p.2))
@[fun_prop] lemma poly_darts : Poly (darts (A := A)) := by
  unfold darts
  apply Poly.list_flatMap
  · fun_prop
  · exact Poly.list_indices.comp Poly.snd
@[fun_prop] lemma poly_endpoint : Poly (fun p : CSPTable A × Dart => endpoint p.1 p.2) := by
  unfold endpoint
  have hr := CSPTable.poly_row (A := A)
  fun_prop
@[fun_prop] lemma poly_incident : Poly (fun p : CSPTable A × ℕ => incident p.1 p.2) := by
  unfold incident
  apply Poly.list_filter
  · fun_prop
  · exact poly_darts.comp Poly.fst
@[fun_prop] lemma poly_active : Poly (active (A := A)) := by
  unfold active
  apply Poly.list_filter
  · fun_prop
  · exact Poly.list_indices.comp Poly.fst
end CloudProgram
end MetricKMedian.PCP.Compiler

end Inline_PCPCloudPrograms

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_AlphabetIndex
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAlphabetIndex
namespace MetricKMedian.PCP.Compiler.AlphabetProgram
open AlphabetReduction Binary Binary.Automatic
open scoped Classical

variable (K : Type) [Fintype K] [DecidableEq K]
noncomputable instance sampleCoding : Coding (EdgeSample K) := finiteCoding _
noncomputable instance sampleHardcoded : Hardcoded (EdgeSample K) := ⟨fun _ _ _ f => finite_function f⟩
@[fun_prop] lemma poly_info : Poly (fun p : Relations K × Tag K => info K p.1 p.2) := hardcoded _
@[fun_prop] lemma poly_allowed : Poly (fun p : Relations K × Tag K => allowed K p.1 p.2) := hardcoded _
@[fun_prop] lemma poly_sampleIndex : Poly (sampleIndex K) := hardcoded _
noncomputable def endpoint (nv : ℕ) (e : ℕ) (r : CSPRow (BitVector K)) (q : Fin 3 × ℕ) : ℕ :=
  if q.1=0 then q.2+B K*r.1 else if q.1=1 then q.2+B K*r.2.1 else nv*B K+(q.2+I K*e)
noncomputable def row (s : CSPTable (BitVector K)) (e : ℕ) (z : Tag K) : CSPRow Label :=
  (s.1.length*B K+s.2.length*I K+(sampleIndex K z.1+S K*e),
    endpoint K s.1.length e (CSPTable.row s e) (info K (CSPTable.row s e).2.2 z),
    allowed K (CSPTable.row s e).2.2 z)
@[fun_prop] lemma poly_endpoint : Poly (fun p : ((ℕ × ℕ) × CSPRow (BitVector K)) × (Fin 3 × ℕ) =>
    endpoint K p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  unfold endpoint
  have h0 : Poly (fun i : Fin 3 => decide (i=0)) := hardcoded _
  have h1 : Poly (fun i : Fin 3 => decide (i=1)) := hardcoded _
  apply Poly.ite_prop (h0.comp (Poly.fst.comp Poly.snd))
  · fun_prop
  · apply Poly.ite_prop (h1.comp (Poly.fst.comp Poly.snd)) <;> fun_prop
@[fun_prop] lemma poly_row : Poly (fun p : (CSPTable (BitVector K) × ℕ) × Tag K => row K p.1.1 p.1.2 p.2) := by
  unfold row
  have hg : Poly (fun p : (CSPTable (BitVector K) × ℕ) × Tag K => CSPTable.row p.1.1 p.1.2) :=
    (CSPTable.poly_row (A := BitVector K)).comp Poly.fst
  have hR := Poly.snd.comp (Poly.snd.comp hg)
  have hq := (poly_info K).comp (Poly.pair hR Poly.snd)
  have ha := (poly_allowed K).comp (Poly.pair hR Poly.snd)
  have he := (poly_endpoint K).comp (Poly.pair (Poly.pair
    (Poly.pair (Poly.list_length.comp (Poly.fst.comp (Poly.fst.comp Poly.fst)))
      (Poly.snd.comp Poly.fst)) hg) hq)
  apply Poly.pair _ (Poly.pair he ha)
  have hsample : Poly (fun p : (CSPTable (BitVector K) × ℕ) × Tag K => sampleIndex K p.2.1) :=
    (poly_sampleIndex K).comp (Poly.fst.comp Poly.snd)
  fun_prop
end MetricKMedian.PCP.Compiler.AlphabetProgram

end Inline_PCPAlphabetIndex

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_RectTables
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPRectTables
namespace MetricKMedian.PCP.Compiler.CSPTable
open Binary Binary.Automatic
open scoped Classical

variable {A T B : Type} [Fintype A] [Coding T] [Coding B]
lemma poly_rect [Inhabited B] (seeds roots : T → List Unit) (tags : List B) (row : T → ℕ → B → CSPRow A)
    (hs : Poly seeds) (hx : Poly roots) (hr : Poly (fun p : (T × ℕ) × B => row p.1.1 p.1.2 p.2)) :
    Poly (fun t => rect (seeds t) (roots t) tags (row t)) := by
  unfold rect
  apply Poly.pair hs
  apply Poly.list_flatMap
  · apply Poly.list_map hr (Automatic.Poly.const tags)
  · exact Poly.list_indices.comp hx
end MetricKMedian.PCP.Compiler.CSPTable

end Inline_PCPRectTables

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_AlphabetTable
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.Walsh.cayley_step _root_.OAI.MetricKMedian.PCP.Walsh.character_sq _root_.OAI.MetricKMedian.PCP.Walsh.character_zero _root_.OAI.MetricKMedian.PCP.Walsh.coefficient_zero
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
noncomputable def seeds (s : CSPTable (BitVector K)) : List Unit :=
  ((s.1.flatMap fun _ => List.replicate (B K) ()) ++
    (s.2.flatMap fun _ => List.replicate (I K) ())) ++
    (s.2.flatMap fun _ => List.replicate (S K) ())
noncomputable def roots (s : CSPTable (BitVector K)) : List Unit := s.2.map (fun _ => ())
lemma seeds_length (s : CSPTable (BitVector K)) :
    (seeds K s).length=s.1.length*B K+s.2.length*I K+s.2.length*S K := by
  unfold seeds
  simp only [List.length_append]
  rw [length_flatMap_uniform s.1 _ (B K) (by intros; simp),
    length_flatMap_uniform s.2 _ (I K) (by intros; simp),
    length_flatMap_uniform s.2 _ (S K) (by intros; simp)]
@[fun_prop] lemma poly_seeds : Poly (seeds K) := by
  unfold seeds
  fun_prop
@[fun_prop] lemma poly_roots : Poly (roots K) := by
  unfold roots
  fun_prop
noncomputable def table (s : CSPTable (BitVector K)) : CSPTable Label :=
  CSPTable.rect (seeds K s) (roots K s) (Ordered.fixed (Tag K)).entries (row K s)
@[fun_prop] lemma poly_table : Poly (table K) := by
  unfold table
  exact CSPTable.poly_rect (seeds K) (roots K) _ (row K) (poly_seeds K) (poly_roots K) (poly_row K)
end MetricKMedian.PCP.Compiler.AlphabetProgram

end Inline_PCPAlphabetTable

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_ApproximationListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Repair
noncomputable def assignmentProgram : PolyProgram (encodePair er er) er (fun x : Row × Row => assignment x.1 x.2) := by
  let coord := (exchange Ratio.encode Ratio.encode).comp ratDiv
  let norm := ((ratSum.fanout (identity er)).comp (coord.listMapWith 0 0))
  exact (weightsProgram.comp norm).congr _ (fun _ => rfl)
noncomputable def assignmentsProgram : PolyProgram (encodePair ers ers) ers (fun x : Rows × Rows => assignments x.1 x.2) :=
  ((listZip er er [] []).comp (assignmentProgram.listMap ([],[]))).congr _ (fun _ => rfl)
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

noncomputable def dominatedProgram : PolyProgram (encodePair er er) encodeBool (fun x : Row × Row => dominated x.1 x.2) := by
  let lo := ((constant (encodePair Ratio.encode Ratio.encode) Ratio.encode 0).fanout (fst Ratio.encode Ratio.encode)).comp ratLE
  let test := (lo.fanout ratLE).comp boolAnd
  exact ((listZip Ratio.encode Ratio.encode 0 0).comp (test.listAll (0,0))).congr _ (fun _ => by simp only [Function.comp_def,dominated,Bool.decide_and])
noncomputable def dotProgram : PolyProgram (encodePair er er) Ratio.encode (fun x : Row × Row => dot x.1 x.2) :=
  ((listZipWith Ratio.encode Ratio.encode 0 0 ratMul).comp ratSum).congr _ (fun _ => rfl)
noncomputable def valueProgram : PolyProgram (encodePair eo ers) Ratio.encode (fun x : Output × Rows => value x.1 x.2) := by
  let xs := (fst eo ers).comp (snd er ers)
  let ds := snd eo ers
  exact (((xs.fanout ds).comp (listZipWith er er [] [] dotProgram)).comp ratSum).congr _ (fun _ => rfl)
end MetricKMedian.LPBinary.Repair
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
def State.step (x : State) : State :=
  State.increment (if x.ctx.t<x.ctx.input.m then
    Bundle.compress (fun c : Context => c.input.n*c.input.m+(c.input.n*c.input.m)*(c.input.n*c.input.m))
      (fun _ => features) x.product else x)

end MetricKMedian.SparseCounts.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_SignedRoundProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
namespace SignedRound

def partialInput (x : Input true) (i : Fin (SparseSignedPartial.run x.β x.p x.n).length) : Input true :=
  ⟨x.n,x.β,(SparseSignedPartial.run x.β x.p x.n).states[i.val],x.positive,
    (SparseSignedPartial.run_invariants _ _ x.feasible _ i).1⟩
def partialInputs (x : Input true) : List (Input true) := List.ofFn (partialInput x)
def boundState (x : Input true) : State true :=
  ⟨x.n,x.β,x.positive,(SparseSignedPartial.run x.β x.p x.n).bindIndexed (SparseSignedRounding.kernel x.β x.p x.feasible)⟩
def result (x : Input true) : State true :=
  ⟨x.n,x.β,x.positive,SparseSignedRounding.round x.β x.p x.feasible⟩

end SignedRound
end MetricKMedian.RoundingProgram
end

end OAI
end


