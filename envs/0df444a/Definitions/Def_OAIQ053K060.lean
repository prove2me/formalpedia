-- Prove2me | Definitions.Def_OAIQ053K060
-- name    : OAIQ053K060
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:13:24.319141+00:00
-- url     : https://prove2.me/theorems/f74789ba-13bd-4bed-9bd3-5557f10ad68c
-- title:
--   Definitions bundle OAIQ053K060 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 29 declarations of OpenAI's Lean: 6 definitions, 1 instance and 22 theorems. The definitions and types are `OAI.MetricKMedian.PCP.Compiler.CSPTable.pullLabels`, `OAI.MetricKMedian.PCP.Compiler.CSPTable.pullRep`, `OAI.MetricKMedian.PCP.Compiler.InitialProgram.bits`, `OAI.MetricKMedian.PCP.Compiler.InitialProgram.bitsRep`, `OAI.MetricKMedian.PCP.Compiler.InitialProgram.table`, `OAI.MetricKMedian.PCP.Compiler.LocalCompiler.represents`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_CookLevin_InitialTable`, `KMedian_Machines_CSPTableBounds`, `KMedian_Machines_FiniteCases`, `KMedian_Machines_FiniteFilterProgram`, `KMedian_Machines_LocalCompiler`, `KMedian_Sparse_SparseGraphRun`, `KMedian_Sparse_SparseOuterCounts`, `KMedian_Sparse_SparseOuterLaw`, `KMedian_Sparse_SparseSignedBudget`, `KMedian_Sparse_SparseSignedPreparation`, `KMedian_Sparse_SparseStarActivation`, `KMedian_Sparse_SparseTargetSubset`, `KMedian_Sparse_SparseWeightedRounding`.
--
--   **Imports.** It imports the bundles `OAIQ053K043`, `OAIQ053K049`, `OAIQ053K050`, `OAIQ053K051`, `OAIQ053K052` and `OAIQ053K053` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K067`, `OAIQ053K068` and `OAIQ053K069`; the proofs of `OAI.MetricKMedian.RationalPhysicalKernel.graph_data_all_s53` and `OAI.MetricKMedian.RationalPhysicalKernel.graph_data_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K043
import Definitions.Def_OAIQ053K049
import Definitions.Def_OAIQ053K050
import Definitions.Def_OAIQ053K051
import Definitions.Def_OAIQ053K052
import Definitions.Def_OAIQ053K053

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_InitialTable
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInitialTable
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic InitialAlphabet
open scoped Classical

namespace CSPTable
variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
noncomputable def pullLabels (f : B→A) (s : CSPTable A) : CSPTable B :=
  (s.1,s.2.map (fun row => (row.1,row.2.1,Finset.univ.filter (fun p => (f p.1,f p.2)∈row.2.2))))
omit [DecidableEq B] in
lemma poly_pullLabels (f : B→A) : Poly (pullLabels f) := by
  have hr : Poly (fun r : Finset (A×A) => Finset.univ.filter (fun p : B×B => (f p.1,f p.2)∈r)) := hardcoded _
  unfold pullLabels
  apply Poly.pair Poly.fst
  apply Poly.list_map _ Poly.snd
  apply Poly.pair (Poly.fst.comp Poly.snd)
  exact Poly.pair (Poly.fst.comp (Poly.snd.comp Poly.snd))
    (hr.comp (Poly.snd.comp (Poly.snd.comp Poly.snd)))
noncomputable def pullRep (f : B→A) (s : CSPTable A) {V E : Type} [Fintype V] [Fintype E]
    {C : BinaryCSP V E A} (r : s.Represents C) : (pullLabels f s).Represents (C.pullLabels f) where
  vertex := r.vertex
  edge := r.edge.trans (finCongr (List.length_map _).symm)
  row e := by
    change (s.2.map _)[(r.edge e).val]=_
    rw [List.getElem_map,r.row]
    rfl
omit [Fintype A] [DecidableEq B] in
lemma pull_wellFormed (f : B→A) {s : CSPTable A} (h : s.WellFormed) : (pullLabels f s).WellFormed := by
  let : Nonempty (Fin s.2.length) := Fin.pos_iff_nonempty.mp h.1
  exact (pullRep f s (self_represents s h)).wellFormed
end CSPTable
namespace InitialProgram
variable (A : Type) [Fintype A] [DecidableEq A] [Nonempty A]
noncomputable def bits (s : CSPTable A) := CSPTable.pullLabels (decode A) s
noncomputable def table (s : CSPTable A) := AlphabetProgram.table A (bits A s)
lemma poly_table : Poly (table A) := (AlphabetProgram.poly_table A).comp (CSPTable.poly_pullLabels (decode A))
variable (s : CSPTable A) (h : s.WellFormed)
include h in
lemma bits_valid : (bits A s).WellFormed := CSPTable.pull_wellFormed _ h
noncomputable def bitsRep : (bits A s).Represents (InitialAlphabet.bits A (s.csp h)) :=
  CSPTable.pullRep (decode A) s (CSPTable.self_represents s h)
end InitialProgram
end MetricKMedian.PCP.Compiler

end Inline_PCPInitialTable

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_CSPTableBounds
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding
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
omit [DecidableEq A] in
lemma poly_check : Poly (check (A := A)) := by
  unfold check
  have hf : Poly (fun s : CSPTable A => s.2.filter fun r => !(decide (r.1 < s.1.length) && decide (r.2.1 < s.1.length))) := by
    apply Poly.list_filter
    · fun_prop
    · exact Poly.snd
  fun_prop
end MetricKMedian.PCP.Compiler.CSPTable

end Inline_PCPCSPTableBounds

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_FiniteCases
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.Compiler.relationCoding _root_.OAI.MetricKMedian.PCP.Compiler.relationHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFiniteCases
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

lemma poly_finite_cases {I X Y : Type} [Fintype I] [Coding I] [Hardcoded I]
    [Coding X] [Coding Y] [Inhabited Y] (f : I → X → Y)
    (h : ∀ i, Poly (f i)) : Poly (fun p : I × X => f p.1 p.2) := by
  let lookup : List I → I × X → Y := fun xs =>
    xs.foldr (fun i g p => if p.1=i then f i p.2 else g p) (fun _ => default)
  have hp : ∀ xs, Poly (lookup xs) := by
    intro xs
    induction xs with
    | nil => exact Automatic.Poly.const _
    | cons i xs ih =>
      change Poly (fun p : I × X => if p.1=i then f i p.2 else lookup xs p)
      exact Poly.ite_prop ((hardcoded (fun j : I => decide (j=i))).comp Poly.fst)
        ((h i).comp Poly.snd) ih
  have he : ∀ xs (i:I) (x:X), i∈xs → lookup xs (i,x)=f i x := by
    intro xs
    induction xs with
    | nil => simp
    | cons j xs ih =>
      intro i x hi
      change (if i=j then f j x else lookup xs (i,x))=f i x
      by_cases hij : i=j
      · simp [hij]
      · rw [ite_eq_right hij]
        exact ih i x ((List.mem_cons.mp hi).resolve_left hij)
  apply poly_congr (hp (Finset.univ.toList))
  intro p
  exact he _ p.1 p.2 (by simp)
end MetricKMedian.PCP.Compiler

end Inline_PCPFiniteCases

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_FiniteFilterProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFiniteFilterProgram
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

namespace FiniteList
variable {A X : Type} [Fintype A] [Coding A] [Hardcoded A] [Coding X] [Inhabited A]
noncomputable instance optionHardcoded : Hardcoded (Option A) := ⟨fun _ _ _ f=>finite_function f⟩

end FiniteList
end MetricKMedian.PCP.Compiler

end Inline_PCPFiniteFilterProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_LocalCompiler
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.CloudCopies.activeNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionCoding _root_.OAI.MetricKMedian.PCP.Compiler.FiniteList.optionHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
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
variable (vars : X→List VC) (tests : X→List TC) (query : X→TC→Q→VC) (accept : X→TC→Finset (Q→A))
variable {V T : Type} [Fintype V] [Fintype T] [DecidableEq V] [DecidableEq T]
variable (C : FiniteCSP V T Q A) (vo : Ordered V) (eo : Ordered T)
  (vc : V→VC) (tc : T→TC) (hvc : Function.Injective vc) (htc : Function.Injective tc)
include hvc htc in
omit [Coding X] [Coding VC] [Coding TC] [Inhabited X] [Inhabited VC] [Inhabited TC]
  [Inhabited Q] [Inhabited A] [Coding Q] [Hardcoded Q] [Fintype V] [Fintype T] in
lemma table_build (x:X) (hv : vars x=vo.entries.map vc) (ht : tests x=eo.entries.map tc)
    (hq : ∀t q, query x (tc t) q=vc (C.query t q))
    (ha : ∀t, accept x (tc t)=C.accept t) :
    table vars tests query accept x=CSPTable.build C.binary (vo.sum eo) (eo.prod (Ordered.fixed Q)) := by
  unfold table CSPTable.build
  apply Prod.ext
  · simp only [hv,ht,Ordered.sum,List.map_append,List.map_map,Function.comp_def]
  · rw [ht]
    simp only [Ordered.prod,List.product,List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def]
    apply congrArg (fun f : T→List (CSPRow (Label (Q := Q) (A := A))) => eo.entries.flatMap f)
    funext t
    apply List.map_congr_left
    intro q hqmem
    unfold row
    rw [hv,ht,hq t q,ha t,← Ordered.index_coded vo vc hvc,← Ordered.index_coded eo tc htc]
    simp only [FiniteCSP.binary,Ordered.sum_left_index,Ordered.sum_right_index,List.length_map,relation]
include hvc htc in
noncomputable def represents (x:X) (hv : vars x=vo.entries.map vc) (ht : tests x=eo.entries.map tc)
    (hq : ∀t q, query x (tc t) q=vc (C.query t q))
    (ha : ∀t, accept x (tc t)=C.accept t) : (table vars tests query accept x).Represents C.binary := by
  rw [table_build vars tests query accept C vo eo vc tc hvc htc x hv ht hq ha]
  exact CSPTable.build_represents _ _ _
end LocalCompiler
end MetricKMedian.PCP.Compiler

end Inline_PCPLocalCompiler

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseGraphRun
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseGraph
open Finset
variable {n m : ℕ}

theorem run_columns (ν : Fin m → SparseIntegerLaw (Finset (Fin n)))
    (P : Fin m → Finset (Fin n) → Prop)
    (hP : ∀ i, ∀ a : Fin (ν i).length, P i (ν i).states[a.val]) (t : ℕ) (ht : t ≤ m) :
    ∀ a : Fin (run ν t).length, ∀ i, i.val<t → P i ((run ν t).states[a.val] i) := by
  induction t with
  | zero => intro a i hi; omega
  | succ t ih =>
    have htm : t < m := by omega
    have he : run ν (t+1)=step (run ν t) (ν ⟨t,htm⟩) ⟨t,htm⟩ := by
      rw [run,dite_eq_left htm]
    let inv : SparseIntegerLaw (Graph n m) → Prop := fun μ =>
      ∀ a : Fin μ.length, ∀ i, i.val<t+1 → P i (μ.states[a.val] i)
    change inv (run ν (t+1))
    rw [he]
    intro a i hi
    obtain ⟨j,k,hjk⟩ := ((run ν t).prodCompress_spec (ν ⟨t,htm⟩)
      (fun G S => next G S ⟨t,htm⟩) features).2.1 a
    change (step (run ν t) (ν ⟨t,htm⟩) ⟨t,htm⟩).states[a.val]=_ at hjk
    rw [hjk]
    by_cases hi' : i=⟨t,htm⟩
    · subst i
      simpa only [next,Function.update_self] using hP ⟨t,htm⟩ k
    · have hiv : i.val≠t := fun h => hi' (Fin.ext h)
      simpa only [next,Function.update_of_ne hi'] using ih (by omega) j i (by omega)

end MetricKMedian.SparseGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseWeightedRounding
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.RationalSignedTerminal.point_state _root_.OAI.MetricKMedian.SparseIntegerLaw.map_states _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect _root_.OAI.MetricKMedian.SparseTargetSubset.point_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseWeightedRounding
open Finset RationalWeightedStep SparseWeightedPartial
variable {n : ℕ}

theorem round_invariants (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1)
    {M : ℚ} (hM : 0 ≤ M) (hβM : ∀ i, β i ≤ M) :
    ∀ a : Fin (round β hβ p).length,
      let q := (round β hβ p).states[a.val]
      (∀ i, point q i=0 ∨ point q i=1) ∧
      |(∑ i, β i*point q i)-(∑ i, β i*point p i)| ≤ M := by
  apply (run β hβ p n).step_property features RationalLastFraction.probability
    RationalLastFraction.probability_unit RationalLastFraction.endpoint
    (fun q => (∀ i, point q i=0 ∨ point q i=1) ∧
      |(∑ i, β i*point q i)-(∑ i, β i*point p i)| ≤ M)
  intro a b
  obtain ⟨ha,hb,hc⟩ := run_invariants β hβ p hp n a
  have hc' : (fractional (run β hβ p n).states[a.val]).card ≤ 1 := by simpa using hc
  refine ⟨RationalLastFraction.endpoint_integral _ ha hc' b,?_⟩
  have hh := RationalLastFraction.endpoint_noise (run β hβ p n).states[a.val] β
    (fun k => (hβ k).le) hβM hM b
  rwa [hb] at hh

end MetricKMedian.SparseWeightedRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseTargetSubset
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.RationalSignedTerminal.point_state _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseTargetSubset
open Finset RationalWeightedStep
variable {n : ℕ}

theorem integral (D : Finset (Fin n)) {q : ℚ} (hq : 0 ≤ q ∧ q ≤ 1)
    (a : Fin (vectors D q).length) : ∀ i, point (vectors D q).states[a.val] i=0 ∨
      point (vectors D q).states[a.val] i=1 :=
  (SparseWeightedRounding.round_invariants (fun _ => 1) (fun _ => by norm_num)
    (initial D q) (initial_unit D hq) (show (0:ℚ) ≤ 1 by norm_num) (fun _ => le_rfl) a).1

theorem mean (D : Finset (Fin n)) {q : ℚ} (hq : 0 ≤ q ∧ q ≤ 1) (i : Fin n) :
    (law D q).moment (fun S => if i∈S then 1 else 0)=if i∈D then q else 0 := by
  rw [law,SparseIntegerLaw.map_moment]
  calc
    _ = (vectors D q).moment (fun p => point p i) :=
      SparseIntegerLaw.moment_congr _ _ _ (fun a =>
        SparseCardinalRounding.selected_indicator _ (integral D hq a) i)
    _ = point (initial D q) i := SparseWeightedRounding.round_mean _ _ _ _
    _ = _ := point_initial D q i

theorem subset (D : Finset (Fin n)) {q : ℚ} (hq : 0 ≤ q ∧ q ≤ 1)
    (a : Fin (law D q).length) : (law D q).states[a.val] ⊆ D := by
  intro i hi
  by_contra hn
  exact (law D q).zero_indicator (fun S => i∈S)
    (by rw [mean D hq i,ite_eq_right hn]) a (positive D q a) hi

theorem fixed (D : Finset (Fin n)) {q : ℚ} (hq : 0 ≤ q ∧ q ≤ 1)
    (a : Fin (law D q).length) :
    (q=0 → (law D q).states[a.val]=∅) ∧ (q=1 → (law D q).states[a.val]=D) := by
  constructor
  · intro hq0
    apply eq_empty_iff_forall_notMem.mpr
    intro i
    exact (law D q).zero_indicator (fun S => i∈S)
      (by rw [mean D hq i,hq0]; split_ifs <;> rfl) a (positive D q a)
  · intro hq1
    apply Subset.antisymm (subset D hq a)
    intro i hi
    exact (law D q).one_indicator (fun S => i∈S)
      (by rw [mean D hq i,ite_eq_left hi,hq1]) a (positive D q a)

theorem count_error (D : Finset (Fin n)) {q : ℚ} (hq : 0 ≤ q ∧ q ≤ 1)
    (a : Fin (law D q).length) :
    |(((law D q).states[a.val]).card:ℚ)-(D.card:ℚ)*q| ≤ 1 := by
  have hh := (SparseWeightedRounding.round_invariants (fun _ => 1) (fun _ => by norm_num)
    (initial D q) (initial_unit D hq) (show (0:ℚ) ≤ 1 by norm_num) (fun _ => le_rfl) a).2
  simp only [one_mul] at hh
  have hsum : (∑ i, point (initial D q) i)=(D.card:ℚ)*q := by
    simp only [point_initial,sum_ite_mem,univ_inter,sum_const,nsmul_eq_mul]
  have hcard : (((law D q).states[a.val]).card:ℚ)=
      ∑ i, point (vectors D q).states[a.val] i := by
    have he := SparseIntegerLaw.map_states (vectors D q) SparseCardinalRounding.selected a
    change (law D q).states[a.val]=_ at he
    rw [he]
    calc
      _ = ∑ i, if i∈SparseCardinalRounding.selected (vectors D q).states[a.val] then (1:ℚ) else 0 := by simp
      _ = _ := sum_congr rfl (fun i _ =>
        SparseCardinalRounding.selected_indicator _ (integral D hq a) i)
  rw [hcard]
  rwa [hsum] at hh

end MetricKMedian.SparseTargetSubset
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseStarActivation
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseStarActivation
open Finset
variable {n m : ℕ}

theorem columns (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ)
    (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) (a : Fin (law D q).length) (e : Fin m) :
    let S := (law D q).states[a.val] e
    S ⊆ D e ∧ |(S.card:ℚ)-((D e).card:ℚ)*q e| ≤ 1 ∧
      (q e=0 → S=∅) ∧ (q e=1 → S=D e) := by
  apply SparseGraph.run_columns (fun e => SparseTargetSubset.law (D e) (q e))
    (fun e S => S ⊆ D e ∧ |(S.card:ℚ)-((D e).card:ℚ)*q e| ≤ 1 ∧
      (q e=0 → S=∅) ∧ (q e=1 → S=D e))
    (fun e b => ⟨SparseTargetSubset.subset (D e) (hq e) b,
      SparseTargetSubset.count_error (D e) (hq e) b,
      SparseTargetSubset.fixed (D e) (hq e) b⟩) m (le_refl m) a e e.isLt

theorem upper_domination (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ)
    (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) (a : Fin (law D q).length) (e : Fin m) (i : Fin n) :
    (if i∈(law D q).states[a.val] e then (1:ℚ) else 0) ≤ upper (q e) := by
  by_cases he : 0 < q e
  · simp only [upper,ite_eq_left he]
    split_ifs <;> norm_num
  · have hz : q e=0 := le_antisymm (le_of_not_gt he) (hq e).1
    rw [(columns D q hq a e).2.2.1 hz]
    simp only [notMem_empty,ite_false,upper,ite_eq_right he,le_refl]

theorem error (D : Fin m → Finset (Fin n)) (q c : Fin m → ℚ)
    (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1) (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1)
    (hsmall : (univ.filter (fun e => 0 < q e ∧ q e < 1)).card ≤ 1)
    (a : Fin (law D q).length) :
    (∑ e, (c e*(upper (q e)-q e)+((D e).card:ℚ)*q e-
      (((law D q).states[a.val] e).card:ℚ))) ≤ 2 := by
  have hq0 : ∀ e, (0:ℝ) ≤ (q e:ℝ) := fun e => by exact_mod_cast (hq e).1
  have hq1 : ∀ e, (q e:ℝ) ≤ 1 := fun e => by exact_mod_cast (hq e).2
  have hc0 : ∀ e, (0:ℝ) ≤ (c e:ℝ) := fun e => by exact_mod_cast (hc e).1
  have hc1 : ∀ e, (c e:ℝ) ≤ 1 := fun e => by exact_mod_cast (hc e).2
  have hs : (MarginalRounding.fractional (fun e => (q e:ℝ))).card ≤ 1 := by
    unfold MarginalRounding.fractional
    have he : (univ.filter (fun e => 0 < (q e:ℝ) ∧ (q e:ℝ)<1))=
        univ.filter (fun e => 0 < q e ∧ q e<1) := by
      apply filter_congr
      intro e _
      norm_cast
    rwa [he]
  have hh := Preparation.exceptional_raw_error D (fun e => (q e:ℝ)) (fun e => (c e:ℝ))
    (law D q).states[a.val] hq0 hq1 hc0 hc1 hs (fun e => ⟨by
      exact_mod_cast (columns D q hq a e).2.1,
      fun he => (columns D q hq a e).2.2.1 (by exact_mod_cast he),
      fun he => (columns D q hq a e).2.2.2 (by exact_mod_cast he)⟩)
  have hu : ∀ e, Preparation.upperBit (q e:ℝ)=(upper (q e):ℝ) := by
    intro e
    simp only [Preparation.upperBit,upper]
    norm_cast
  simp_rw [hu] at hh
  exact_mod_cast hh

end MetricKMedian.SparseStarActivation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSignedPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedPreparation
open Finset
open RationalWeightedStep (point fractional)
variable {n m : ℕ}

theorem kernel_nominal (D : Fin m → Finset (Fin n)) (q : Vector ℚ m)
    (hq : ∀ e, 0 ≤ point q e ∧ point q e ≤ 1) (e : Fin m) :
    (kernel D q hq).moment (fun z => SparseBernoulli.flag z.2.2 e)=point q e := by
  rw [kernel,SparseIntegerLaw.prod_moment]
  simp only [SparseBernoulli.single_moment,SparseIntegerLaw.moment_const]

end MetricKMedian.SparseSignedPreparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSignedBudget
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.SparseBernoulli.cast_flag _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedPreparation
open Finset
open RationalWeightedStep (point fractional)
variable {n m : ℕ}

theorem kernel_budget (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (b : Fin m → ℕ)
    (q : Vector ℚ m) (hq : ∀ e, 0 ≤ point q e ∧ point q e ≤ 1)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hsmall : (fractional q).card ≤ 1) :
    ∀ a : Fin (kernel D q hq).length,
      BudgetSpec D c b ((∑ e, signed D c e*((b e:ℚ)+point q e))+2)
        (kernel D q hq).states[a.val] := by
  unfold kernel
  apply SparseIntegerLaw.prod_property (SparseStarActivation.law D (point q))
    (SparseBernoulli.run (d := 2) (point q) hq m) (fun S ω => (q,S,ω))
    (BudgetSpec D c b _)
  intro a d
  dsimp only [BudgetSpec]
  refine ⟨fun e => (SparseStarActivation.columns D (point q) hq a e).1,?_,?_,?_,?_,?_⟩
  · intro e
    dsimp only [outside,SparseStarActivation.upper]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl (add_zero _)
  · intro e
    dsimp only [nominalCount,SparseBernoulli.flag]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl (add_zero _)
  · intro e
    dsimp only [nominalCount,outside]
    rw [add_le_add_iff_left]
    by_cases he : 0 < point q e
    · simp only [SparseStarActivation.upper,ite_eq_left he,SparseBernoulli.flag]
      split_ifs <;> norm_num
    · have hz : point q e=0 := le_antisymm (le_of_not_gt he) (hq e).1
      have hh := SparseBernoulli.fixed (point q) hq d e (Or.inl hz)
      rw [hh,hz]
      simp only [SparseStarActivation.upper,lt_self_iff_false,ite_false,le_refl]
  · intro e i
    dsimp only [outside]
    rw [add_le_add_iff_left]
    exact SparseStarActivation.upper_domination D (point q) hq a e i
  · have hh := SparseStarActivation.error D (point q) c hq hc hsmall a
    have he : raw D c b (q,(SparseStarActivation.law D (point q)).states[a.val],
        (SparseBernoulli.run (d := 2) (point q) hq m).states[d.val])=
        (∑ e, signed D c e*((b e:ℚ)+point q e))+
        ∑ e, (c e*(SparseStarActivation.upper (point q e)-point q e)+
          ((D e).card:ℚ)*point q e-
          (((SparseStarActivation.law D (point q)).states[a.val] e).card:ℚ)) := by
      unfold raw
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro e _
      dsimp only [raw,outside,signed]
      ring
    rw [he]
    linarith only [hh]

theorem law_budget (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (b : Fin m → ℕ)
    (p : Vector ℚ m) (hp : ∀ e, 0 ≤ point p e ∧ point p e ≤ 1)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) :
    ∀ a : Fin (law D c p hp hc).length,
      BudgetSpec D c b ((∑ e, signed D c e*((b e:ℚ)+point p e))+3)
        (law D c p hp hc).states[a.val] := by
  unfold law
  apply SparseIntegerLaw.bindIndexed_property _ _ (BudgetSpec D c b _)
  intro a d
  let hu : ∀ e, 0 < signed D c e → signed D c e ≤ 1 := fun e _ =>
    (sub_le_self _ (Nat.cast_nonneg _)).trans (hc e).2
  have ha := SparseSignedRounding.round_invariants (signed D c) p hp hu a
  have hh := kernel_budget D c b (SparseSignedRounding.round (signed D c) p hp).states[a.val]
    ha.1 hc ha.2.1 d
  refine ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.1,?_⟩
  have hb : (∑ e, signed D c e*((b e:ℚ)+point (SparseSignedRounding.round (signed D c) p hp).states[a.val] e)) ≤
      (∑ e, signed D c e*((b e:ℚ)+point p e))+1 := by
    simp only [mul_add,sum_add_distrib]
    linarith only [ha.2.2]
  exact hh.2.2.2.2.2.trans (by linarith only [hb])

end MetricKMedian.SparseSignedPreparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseOuterLaw
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open RationalWeightedStep (point)
open SparseGridRounding (base fraction)
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem budget (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) :
    ∀ a : Fin (law D c q hc hq).length,
      SparseSignedPreparation.BudgetSpec D c (base q)
        ((∑ e,SparseSignedPreparation.signed D c e*q e)+3) (law D c q hc hq).states[a.val] := by
  have hh := SparseSignedPreparation.law_budget D c (base q) (fraction q)
    (SparseGridRounding.fraction_unit q hq) hc
  simpa only [fraction_identity] using hh

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseOuterCounts
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open RationalWeightedStep (point)
open SparseGridRounding (base fraction)
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem activationCount_support (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e)
    (a : Fin (law D c q hc hq).length) (e : Fin m) (i : Fin n) (hi : i∉D e) :
    activationCount D q (law D c q hc hq).states[a.val] e i=0 := by
  have hh : i∉(law D c q hc hq).states[a.val].2.1 e := fun hh => hi ((budget D c q hc hq a).1 e hh)
  simp only [activationCount,ite_eq_right hi,ite_eq_right hh,Nat.add_zero]

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end


