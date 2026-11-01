-- Prove2me | Definitions.Def_OAIQ053K058
-- name    : OAIQ053K058
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:12:22.433448+00:00
-- url     : https://prove2.me/theorems/a968dc41-a79b-4c3a-9d66-04ad799d6232
-- title:
--   Definitions bundle OAIQ053K058 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 48 declarations of OpenAI's Lean: 20 definitions and 28 theorems. The definitions and types are `OAI.MetricKMedian.Instance.computedPseudo`, `OAI.MetricKMedian.Instance.fractionalRound`, `OAI.MetricKMedian.Instance.nonzeroRound`, `OAI.MetricKMedian.InstanceProgram.fractionalInput`, `OAI.MetricKMedian.LPBinary.Repair.validProgram`, `OAI.MetricKMedian.LPBinary.Scale.guessesProgram`, `OAI.MetricKMedian.PCP.Compiler.RegularProgram.allowed`, `OAI.MetricKMedian.PCP.Compiler.RegularProgram.localAllowed`, `OAI.MetricKMedian.PCP.Compiler.RegularProgram.localRotate`, `OAI.MetricKMedian.PCP.Compiler.RegularProgram.matchAllowed`, `OAI.MetricKMedian.PCP.Compiler.RegularProgram.matchStep`, `OAI.MetricKMedian.PCP.Compiler.RegularProgram.paddedAllowed`, `OAI.MetricKMedian.PCP.Compiler.RegularProgram.paddedRotate`, `OAI.MetricKMedian.PCP.Compiler.RegularProgram.strongRotate`, `OAI.MetricKMedian.SparsePrepared.Program.Input.ker`, `OAI.MetricKMedian.SparsePrepared.Program.Input.kernels`, `OAI.MetricKMedian.SparsePrepared.Program.Input.μ`, `OAI.MetricKMedian.SparsePrepared.Program.KernelInput.base`, `OAI.MetricKMedian.SparseSignedPreparation.Program.Input.ker`, `OAI.MetricKMedian.SparseSignedPreparation.Program.Input.kernels`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Amplification_RegularPrograms`, `KMedian_Binary_NumericParserProgram`, `KMedian_Expanders_CloudPrograms`, `KMedian_Expanders_ExpanderCompiler`, `KMedian_Machines_RawSquare`, `KMedian_Machines_RotationBounds`, `KMedian_Optimization_FractionalListChecks`, `KMedian_Preparation_PreparedDataOperations`, `KMedian_Preparation_PreparedLawProgram`, `KMedian_Preparation_RepresentativeProgram`, `KMedian_Process_CountRunHeight`, `KMedian_Process_CountRunProgram`, `KMedian_Programs_InstanceComputedPseudo`, `KMedian_Programs_InstanceDataProgram`, `KMedian_Programs_InstanceFractionalRound`, `KMedian_Programs_ScaleListProgram`, `KMedian_Rounding_SignedPreparationProgram`, `KMedian_Sparse_SparseCountRun`.
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundles `OAIQ053K048`, `OAIQ053K049`, `OAIQ053K050`, `OAIQ053K051` and `OAIQ053K052` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K066`, `OAIQ053K067` and `OAIQ053K068`; the statement `OAI.MetricKMedian.Instance.computedPseudo_spec_s53`; the proof of `OAI.MetricKMedian.Instance.computedPseudo_spec_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K048
import Definitions.Def_OAIQ053K049
import Definitions.Def_OAIQ053K050
import Definitions.Def_OAIQ053K051
import Definitions.Def_OAIQ053K052

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_RotationBounds
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.relationCoding
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
lemma size_bound {R : RotationTable D} (h : WellFormed R) (N : ℕ) (hN : R.length ≤ N) :
    (enc R).length ≤ sizeBound (D := D) N := by
  have he (q : ℕ × D) (hq : q.1<R.length) : (enc q).length ≤ 2*(N+1)+1+codeBound (D := D) := by
    have hn : q.1.bits.length ≤ N+1 := (NatBinary.length_le_height (Nat.lt_two_pow_self.le)).trans (by omega)
    have hd := code_le q.2
    change (encodePair Nat.bits enc q).length ≤ _
    rw [encodePair_length]
    omega
  have hr (row : List (ℕ × D)) (hm : row∈R) :
      (enc row).length ≤ Fintype.card D*(2*(2*(N+1)+1+codeBound (D := D))+1) := by
    change (encodeList (enc (α := ℕ × D)) row).length ≤ _
    have hh := h row hm
    simpa only [hh.1] using EncodedList.length_bound enc row _ (fun q hq => he q (hh.2 q hq))
  change (encodeList (enc (α := List (ℕ × D))) R).length ≤ _
  exact (EncodedList.length_bound enc R _ hr).trans (Nat.mul_le_mul_right _ hN)
end MetricKMedian.PCP.Compiler.RotationTable

end Inline_PCPRotationBounds

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_ExpanderCompiler
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPExpanderCompiler
namespace MetricKMedian.PCP.Compiler.Expander
open ExpanderFamily RotationTable Binary Binary.Automatic Polynomial
open scoped Classical

lemma reachable_size (xs : List Unit) (i : ℕ) :
    (enc (guarded^[i] (xs.length,initial))).length ≤ sizePoly.eval (enc xs).length := by
  rw [iterate_guarded]
  have ht := size_bound (sequence_wellFormed xs.length i) _ (sequence_length xs.length i)
  have hn : xs.length ≤ (enc xs).length := EncodedList.length_le _ _
  have hb : xs.length.bits.length ≤ xs.length+1 :=
    NatBinary.length_le_height (Nat.lt_two_pow_self (n := xs.length)).le
  change (encodePair Nat.bits enc (sequence xs.length i)).length ≤ _
  rw [encodePair_length]
  change 2*xs.length.bits.length+1+(enc (sequence xs.length i).2).length ≤ _
  apply (Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hb) 1) ht).trans
  unfold sizeBound sizePoly
  simp only [eval_add,eval_mul,eval_X,eval_C,eval_one,eval_ofNat]
  gcongr
lemma poly_trajectory : Poly (fun xs : List Unit =>
    Iteration.iterates guarded (xs.length,initial) (xs.length+2)) := by
  refine ⟨poly_guarded.program.iteratesFrom poly_initialState.program poly_steps.program
    (0,initial) (X+2) sizePoly ?_ ?_⟩
  · intro xs
    have h : xs.length ≤ (enc xs).length := EncodedList.length_le _ _
    simpa only [eval_add,eval_X,eval_ofNat] using Nat.add_le_add_right h 2
  · intro xs i hi
    exact reachable_size xs i
lemma poly_generate : Poly generate := by
  have hi : Poly (fun xs : List Unit => xs.length+1) := by fun_prop
  have hg := Poly.list_getD_comp (0,initial) poly_trajectory hi
  apply poly_congr (Poly.snd.comp hg)
  intro xs
  change ((Iteration.iterates guarded (xs.length,initial) (xs.length+2))[xs.length+1]?.getD
    (0,initial)).2=generate xs
  rw [Iteration.iterates_eq]
  simp only [List.getElem?_map,List.getElem?_range,show xs.length+1<xs.length+2 by omega,
    Option.map_some,Option.getD_some,generate]
end MetricKMedian.PCP.Compiler.Expander

end Inline_PCPExpanderCompiler

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Expanders_CloudPrograms
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCloudPrograms
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

namespace CloudProgram
variable {A : Type} [Fintype A]
@[fun_prop] lemma poly_cloud : Poly (fun p : CSPTable A × ℕ => cloud p.1 p.2) := by
  unfold cloud
  apply Expander.poly_generate.comp
  apply Poly.list_map
  · exact Automatic.Poly.const _
  · exact Poly.list_tail.comp poly_incident
@[fun_prop] lemma poly_nodes : Poly (nodes (A := A)) := by
  unfold nodes
  apply Poly.list_flatMap
  · apply Poly.list_map
    · fun_prop
    · exact Poly.list_indices.comp poly_cloud
  · exact poly_active
@[fun_prop] lemma poly_global : Poly (global (A := A)) := by
  unfold global
  apply Expander.poly_generate.comp
  apply Poly.list_map
  · exact Automatic.Poly.const _
  · exact Poly.list_tail.comp poly_nodes
@[fun_prop] lemma poly_index : Poly (fun p : CSPTable A × (ℕ × ℕ) => index p.1 p.2) := by
  unfold index
  apply Poly.list_findIdx
  · have he : Poly (fun p : ((CSPTable A × (ℕ × ℕ)) × (ℕ × ℕ)) =>
        decide (p.2.1=p.1.2.1) && decide (p.2.2=p.1.2.2)) := by fun_prop
    simpa only [Bool.decide_and] using he
  · exact poly_nodes.comp Poly.fst
@[fun_prop] lemma poly_dartIndex : Poly (fun p : (CSPTable A × ℕ) × Dart => dartIndex p.1.1 p.1.2 p.2) := by
  unfold dartIndex
  apply Poly.list_findIdx
  · have he : Poly (fun p : (((CSPTable A × ℕ) × Dart) × Dart) =>
        decide (p.2.1=p.1.2.1) && decide (p.2.2=p.1.2.2)) := by
      have hb : Poly (fun p : Bool × Bool => decide (p.1=p.2)) := hardcoded _
      have hb' := hb.comp (show Poly (fun p : (((CSPTable A × ℕ) × Dart) × Dart) => (p.2.2,p.1.2.2)) by fun_prop)
      fun_prop
    simpa only [Bool.decide_and] using he
  · exact poly_incident.comp Poly.fst
end CloudProgram
end MetricKMedian.PCP.Compiler

end Inline_PCPCloudPrograms

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_RawSquare
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.relationCoding _root_.OAI.MetricKMedian.PCP.Compiler.relationHardcoded
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
@[fun_prop] lemma poly_squareLookup : Poly (fun p : (RotationTable D × ℕ) × (D × D) => squareLookup p.1.1 p.1.2 p.2) := by
  unfold squareLookup
  have hl := poly_lookup (D := D)
  fun_prop
@[fun_prop] lemma poly_fourthLookup : Poly (fun p : (RotationTable D × ℕ) × ((D × D) × (D × D)) => fourthLookup p.1.1 p.1.2 p.2) := by
  unfold fourthLookup squareLookup
  have hl := poly_lookup (D := D)
  fun_prop
lemma poly_fourthLookup_comp {X : Type} [Coding X] (R : X → RotationTable D) (v : X → ℕ)
    (d : X → ((D × D) × (D × D))) (hR : Poly R) (hv : Poly v) (hd : Poly d) :
    Poly (fun x => fourthLookup (R x) (v x) (d x)) :=
  poly_fourthLookup.comp (Poly.pair (Poly.pair hR hv) hd)
end MetricKMedian.PCP.Compiler.RotationTable

end Inline_PCPRawSquare

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_RegularPrograms
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
@[fun_prop] lemma poly_zeroBranch : Poly (fun i : Fin 3 => decide (i=0)) := hardcoded _
noncomputable def matchStep (t : CSPTable A) (p : ℕ × ℕ) : ℕ × ℕ :=
  let ds := incident t p.1
  if p.2<ds.length then
    let d := ds[p.2]?.getD (0,false)
    let e := (d.1,!d.2)
    let v := endpoint t e
    (v,dartIndex t v e)
  else p
noncomputable def matchAllowed (t : CSPTable A) (p : ℕ × ℕ) : Finset (A × A) :=
  let ds := incident t p.1
  if p.2<ds.length then
    let d := ds[p.2]?.getD (0,false)
    let rel := (CSPTable.row t d.1).2.2
    if d.2 then rel.image Prod.swap else rel
  else Finset.univ
noncomputable def localRotate (t : CSPTable A) (p : ℕ × ℕ) (d : RPort) : (ℕ × ℕ) × RPort :=
  if d.1=0 then (matchStep t p,d) else
    let q := lookup (cloud t p.1) p.2 d.2.2
    ((p.1,q.1),(d.1,(d.2.1,q.2)))
noncomputable def localAllowed (t : CSPTable A) (p : ℕ × ℕ) (d : RPort) : Finset (A × A) :=
  if d.1=0 then matchAllowed t p else Finset.univ.filter (fun a => a.1=a.2)
noncomputable def paddedRotate (t : CSPTable A) (v : ℕ) (d : RPort) : ℕ × RPort :=
  if v<(nodes t).length then
    let p := (nodes t)[v]?.getD (0,0)
    let q := localRotate t p d
    (index t q.1,q.2)
  else (v,d)
noncomputable def paddedAllowed (t : CSPTable A) (v : ℕ) (d : RPort) : Finset (A × A) :=
  if v<(nodes t).length then localAllowed t ((nodes t)[v]?.getD (0,0)) d else Finset.univ
noncomputable def strongRotate (t : CSPTable A) (v : ℕ) (d : GlobalRegularization.StrongPort) : ℕ × GlobalRegularization.StrongPort :=
  RotationTable.fourthLookup (global t) v d
noncomputable def allowed (t : CSPTable A) (v : ℕ) (d : Port) : Finset (A × A) :=
  if d.1=0 then paddedAllowed t v d.2.1 else Finset.univ
@[fun_prop] lemma poly_matchStep : Poly (fun s : CSPTable A × (ℕ × ℕ) => matchStep s.1 s.2) := by
  unfold matchStep
  dsimp only
  apply Poly.ite_prop
  · fun_prop
  · let f : CSPTable A × (ℕ × ℕ) → Dart := fun x =>
      let d := (incident x.1 x.2.1)[x.2.2]?.getD (0,false)
      (d.1,!d.2)
    have hf : Poly f := by unfold f; fun_prop
    have he : Poly (fun x : CSPTable A × (ℕ × ℕ) => endpoint x.1 (f x)) :=
      poly_endpoint.comp (Poly.pair Poly.fst hf)
    have hi := poly_dartIndex.comp (Poly.pair (Poly.pair Poly.fst he) hf)
    exact Poly.pair he hi
  · fun_prop
@[fun_prop] lemma poly_matchAllowed : Poly (fun s : CSPTable A × (ℕ × ℕ) => matchAllowed s.1 s.2) := by
  have ht : Poly (fun r : Finset (A × A) => r.image Prod.swap) := hardcoded _
  have hr := CSPTable.poly_row (A := A)
  unfold matchAllowed
  fun_prop
@[fun_prop] lemma poly_localRotate : Poly (fun s : (CSPTable A × (ℕ × ℕ)) × RPort => localRotate s.1.1 s.1.2 s.2) := by
  unfold localRotate
  dsimp only
  apply Poly.ite_prop
  · exact poly_zeroBranch.comp (Poly.fst.comp Poly.snd)
  · have hm := poly_matchStep (A := A)
    fun_prop
  · have hl := RotationTable.poly_lookup (D := ExpanderFamily.Degree)
    fun_prop
@[fun_prop] lemma poly_localAllowed : Poly (fun s : (CSPTable A × (ℕ × ℕ)) × RPort => localAllowed s.1.1 s.1.2 s.2) := by
  unfold localAllowed
  apply Poly.ite_prop
  · exact poly_zeroBranch.comp (Poly.fst.comp Poly.snd)
  · exact poly_matchAllowed.comp (by fun_prop)
  · exact Automatic.Poly.const _
@[fun_prop] lemma poly_paddedRotate : Poly (fun s : (CSPTable A × ℕ) × RPort => paddedRotate s.1.1 s.1.2 s.2) := by
  unfold paddedRotate
  dsimp only
  apply Poly.ite_prop
  · fun_prop
  · have hp : Poly (fun x : (CSPTable A × ℕ) × RPort => ((nodes x.1.1)[x.1.2]?.getD (0,0))) := by fun_prop
    have hl := poly_localRotate.comp (Poly.pair (Poly.pair (Poly.fst.comp Poly.fst) hp) Poly.snd)
    exact Poly.pair (poly_index.comp (Poly.pair (Poly.fst.comp Poly.fst) (Poly.fst.comp hl))) (Poly.snd.comp hl)
  · fun_prop
@[fun_prop] lemma poly_paddedAllowed : Poly (fun s : (CSPTable A × ℕ) × RPort => paddedAllowed s.1.1 s.1.2 s.2) := by
  unfold paddedAllowed
  apply Poly.ite_prop
  · fun_prop
  · have hp : Poly (fun x : (CSPTable A × ℕ) × RPort => ((nodes x.1.1)[x.1.2]?.getD (0,0))) := by fun_prop
    exact poly_localAllowed.comp (Poly.pair (Poly.pair (Poly.fst.comp Poly.fst) hp) Poly.snd)
  · exact Automatic.Poly.const _
@[fun_prop] lemma poly_strongRotate : Poly (fun s : (CSPTable A × ℕ) × GlobalRegularization.StrongPort => strongRotate s.1.1 s.1.2 s.2) := by
  unfold strongRotate
  apply RotationTable.poly_fourthLookup_comp (D := ExpanderFamily.Degree)
  · exact poly_global.comp (Poly.fst.comp Poly.fst)
  · exact Poly.snd.comp Poly.fst
  · exact Poly.snd
end MetricKMedian.PCP.Compiler.RegularProgram

end Inline_PCPRegularPrograms

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_NumericParserProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.InputParser
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
 theorem ratRead_append (q : ℚ) (xs : List Bool) : ratRead (encodeRat q++xs)=(q,xs) := by
  simp only [ratRead,encodeRat,List.append_assoc,List.cons_append,List.tail_cons,List.head?_cons,Option.getD_some,List.nil_append,natRead_append]
  rw [show Signed.value (decide (q.num<0)) q.num.natAbs=q.num from Signed.value_parts q.num]
  rw [Rat.mkRat_eq_div,q.num_div_den]
end MetricKMedian.InputParser
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_FractionalListChecks
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.LPBinary.Repair
open Binary Binary.PolyProgram Function Finset

noncomputable def validProgram : PolyProgram (encodePair eo Nat.bits) encodeBool (fun x : Output × ℕ => valid x.1 x.2) := by
  let a := fst eo Nat.bits
  let ys := a.comp (fst er ers)
  let xs := a.comp (snd er ers)
  let k := ((snd eo Nat.bits).comp ratOfNat).fanout (constant (encodePair eo Nat.bits) Ratio.encode 1) |>.comp ratAdd
  let yb := ys.comp (boundedProgram.listAll 0)
  let rowDom := (exchange er er).comp dominatedProgram
  let dom := (ys.fanout xs).comp (rowDom.listAllWith [])
  let one := ((ratSum.fanout (constant er Ratio.encode 1)).comp ratEQ).listAll []
  let sums := xs.comp one
  let cap := ((ys.comp ratSum).fanout k).comp ratLE
  exact (((((yb.fanout dom).comp boolAnd).fanout sums).comp boolAnd).fanout cap |>.comp boolAnd).congr _ (fun _ => rfl)
end MetricKMedian.LPBinary.Repair
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_SignedPreparationProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.SparseSignedPreparation.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
def Input.ker (x : Input) (i : Fin x.μ.length) : KernelInput :=
  ⟨x.n,x.m,x.D,x.μ.states[i.val],
    (SparseSignedRounding.round_invariants (SparseSignedPreparation.signed x.D x.c) x.p x.feasible (fun e _ =>
      (sub_le_self _ (Nat.cast_nonneg _)).trans (x.c_unit e).2) i).1⟩
def Input.kernels (x : Input) := List.ofFn x.ker

end MetricKMedian.SparseSignedPreparation.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseCountRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseCounts
open Finset
variable {n m : ℕ}

theorem run_length (ν : Fin m → SparseIntegerLaw ((Fin n → ℕ))) (t : ℕ) :
    (run ν t).length ≤ n*m+(n*m)*(n*m)+1 := by
  induction t with
  | zero => change 1 ≤ _; omega
  | succ t ih =>
    rw [run]
    split_ifs with ht
    · exact ((run ν t).prodCompress_spec (ν ⟨t,ht⟩)
        (fun G S => next G S ⟨t,ht⟩) features).1
    · exact ih

end MetricKMedian.SparseCounts
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparedDataOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.SparsePrepared.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (setView indices)

def KernelInput.base (x : KernelInput) : BaseRaw :=
  (List.ofFn (fun e => setView (x.D e)),(List.ofFn x.q,(List.ofFn (fun j => setView (x.P j)),
    (List.ofFn x.y,(List.ofFn x.p,x.Δ)))))
end MetricKMedian.SparsePrepared.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CountRunHeight
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.SparseIntegerLaw.map_states _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseCounts
open Binary
variable {n m : ℕ}

theorem run_bound (ν : Fin m → SparseIntegerLaw (Fin n → ℕ)) (U : ℕ)
    (hν : ∀ i, ∀ a : Fin (ν i).length, ∀ h, (ν i).states[a.val] h≤U) (t : ℕ) :
    ∀ a : Fin (run ν t).length, ∀ i h,(run ν t).states[a.val] i h≤U := by
  induction t with
  | zero =>
    intro a i h
    change (Vector.replicate 1 (fun _ : Fin m => fun _ : Fin n => (0:ℕ)))[a.val] i h≤U
    simp only [Vector.getElem_replicate]
    exact Nat.zero_le _
  | succ t ih =>
    let P := fun μ : SparseIntegerLaw (Table n m) => ∀ a : Fin μ.length, ∀ i h,μ.states[a.val] i h≤U
    change P (run ν (t+1))
    rw [run]
    split_ifs with ht
    · intro a i h
      obtain ⟨j,k,hjk⟩ := ((run ν t).prodCompress_spec (ν ⟨t,ht⟩)
        (fun G S => next G S ⟨t,ht⟩) features).2.1 a
      change (step (run ν t) (ν ⟨t,ht⟩) ⟨t,ht⟩).states[a.val]=_ at hjk
      rw [hjk]
      exact next_bound _ _ _ U (ih j) (hν _ k) i h
    · exact ih

theorem denominator_height (ν : Fin m → SparseIntegerLaw (Fin n → ℕ)) (N L H : ℕ)
    (hN : ∀ i, (ν i).length≤N) (hL : ∀ i, (ν i).law.denominator≤(2:ℤ)^L)
    (hν : ∀ i, ∀ a : Fin (ν i).length, ∀ h, (ν i).states[a.val] h≤2^H) (t : ℕ) :
    (run ν t).law.denominator≤(2:ℤ)^(stepHeight n m N L H*t) := by
  induction t with
  | zero => simp [run,SparseIntegerLaw.dirac]
  | succ t ih =>
    rw [run]
    split_ifs with ht
    · rw [dite_eq_left ht]
      let μ := run ν t
      let ρ := μ.prod (ν ⟨t,ht⟩) (fun G S => next G S ⟨t,ht⟩)
      have hr : ∀ a : Fin ρ.length, ∀ i h,ρ.states[a.val] i h≤2^H := by
        apply SparseIntegerLaw.prod_property μ (ν ⟨t,ht⟩) (fun G S => next G S ⟨t,ht⟩) (fun G => ∀ i h,G i h≤2^H)
        intro a b
        exact next_bound _ _ _ _ (run_bound ν _ hν t a) (hν _ b)
      have hc := ρ.compressAuto_denominator features (H+H)
        (fun i a => (features_height ρ.states[i.val] H (hr i) a).1)
        (fun i a => (features_height ρ.states[i.val] H (hr i) a).2)
      have hrD : ρ.law.denominator=μ.law.denominator*(ν ⟨t,ht⟩).law.denominator := rfl
      have hrN : ρ.length ≤ (n*m+(n*m)*(n*m)+1)*N :=
        Nat.mul_le_mul (run_length ν t) (hN _)
      change (ρ.compressAuto features).law.denominator≤_
      apply hc.trans
      rw [hrD]
      calc
        _ ≤ ((2:ℤ)^(stepHeight n m N L H*t)*(2:ℤ)^L)*
            (2:ℤ)^((2*(n*m+(n*m)*(n*m)+1)*(n*m+(n*m)*(n*m)+1+
              (H+H)*((n*m+(n*m)*(n*m)+1)*N+1)))*
              ((n*m+(n*m)*(n*m)+1)*N+1)*((n*m+(n*m)*(n*m)+1)*N)) := by
          gcongr
          · exact (ν ⟨t,ht⟩).law.denominator_pos.le
          · exact hL _
          · norm_num
        _ = _ := by rw [← pow_add,← pow_add]; congr 1; simp only [stepHeight]; ring
    · rw [dite_eq_right ht]
      exact ih.trans (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ (Nat.le_succ t)))
end MetricKMedian.SparseCounts
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CountRunProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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

theorem state_next (x : Input) (t : ℕ) : State.step (x.state t)=x.state (t+1) := by
  have he (ht : t < x.m) : update ⟨x,t⟩=(fun G S => next G S ⟨t,ht⟩) := by
    funext G S i
    by_cases h : i=⟨t,ht⟩
    · subst i; simp only [update,next,Function.update_self,ite_true]
    · have hv : i.val≠t := fun hh => h (Fin.ext hh)
      simp only [update,next,Function.update_of_ne h,ite_eq_right hv]
  unfold State.step Input.state
  by_cases ht : t < x.m
  · rw [ite_eq_left ht]
    change (⟨⟨x,t+1⟩,((run x.columns t).prod (column ⟨x,t⟩) (update ⟨x,t⟩)).compressAuto features⟩ : State)=_
    rw [run,dite_eq_left ht]
    simp only [column,dite_eq_left ht,he ht,SparseCounts.step,SparseIntegerLaw.prodCompress]
  · rw [ite_eq_right ht,run,dite_eq_right ht]
    rfl

theorem state_iterate (x : Input) (t : ℕ) : (State.step)^[t] x.start=x.state t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,state_next]

end MetricKMedian.SparseCounts.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparedLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.SparsePrepared.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (setView)
def Input.μ (x : Input) := SparseOuterLaw.law x.D x.c x.q x.hc x.hq
def Input.ker (x : Input) (i : Fin x.μ.length) : KernelInput :=
  ⟨x.n,x.m,x.f,x.D,x.q,x.P,x.y,x.p,x.Δ,x.μ.states[i.val],x.hy,x.hp⟩
def Input.kernels (x : Input) := List.ofFn x.ker

end MetricKMedian.SparsePrepared.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RepresentativeProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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

 theorem any_view {n : ℕ} (U : Finset (Fin n)) : (setView U).any id=decide U.Nonempty := by
  apply Bool.eq_iff_iff.mpr
  simp only [setView,List.any_eq_true,List.mem_ofFn,id_eq,decide_eq_true_eq]
  constructor
  · rintro ⟨b,⟨i,rfl⟩,hi⟩; exact ⟨i,of_decide_eq_true hi⟩
  · rintro ⟨i,hi⟩; exact ⟨_,⟨i,rfl⟩,decide_eq_true hi⟩

end MetricKMedian.Preparation.RationalRepresentatives.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_InstanceFractionalRound
attribute [-instance] _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.Instance
open Finset Preparation

 def fractionalRound (I : Instance) (a : TruncatedLP.FractionalData I.facilities.card I.clients.card)
    (ha : a.Valid I.k) (hj : I.clients.Nonempty) {η τ : ℝ} (p : RationalAllParameters η τ) (C : ℕ) :
    Option (Finset (Fin I.n)) :=
  letI := I.pseudoMetric
  (FractionalRefinement.scan a I.k ha (card_pos.mpr hj) I.indexedDistance I.clientDistance I.facilityDistance
    I.indexedDistance_nonneg I.clientDistance_self I.clientDistance_comm
    (I.facilities.orderEmbOfFin rfl) (I.clients.orderEmbOfFin rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) p (I.k+C)).map
    (fun O => O.image (I.facilities.orderEmbOfFin rfl))

end MetricKMedian.Instance
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_InstanceComputedPseudo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Instance
open Finset Preparation

 theorem nonzeroFractional_spec (I : Instance) (h : ¬I.zeroTest) (r : ℕ) (hr : 0 < r) :
    let a := I.computedFractional r hr (I.nonzero_clients h)
    a.Valid I.k ∧ (a.value I.indexedDistance:ℝ)≤(1+3/(r:ℝ))*optimum I := by
  simpa only [dite_eq_right h] using I.initialPhase_spec r hr

 def nonzeroRound (I : Instance) (h : ¬I.zeroTest) (r : ℕ) (hr : 0 < r)
    {η τ : ℝ} (p : RationalAllParameters η τ) (C : ℕ) : Option (Finset (Fin I.n)) :=
  I.fractionalRound (I.computedFractional r hr (I.nonzero_clients h))
    (I.nonzeroFractional_spec h r hr).1 (I.nonzero_clients h) p C

 def computedPseudo (I : Instance) (r : ℕ) (hr : 0 < r)
    {η τ : ℝ} (p : RationalAllParameters η τ) (C : ℕ) : Finset (Fin I.n) :=
  if h : I.zeroTest then I.zeroOutput
  else (I.nonzeroRound h r hr p C).getD {I.facilities.min' I.facilities_nonempty}

end MetricKMedian.Instance
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_ScaleListProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Scale

noncomputable def guessesProgram : PolyProgram ers er guesses := by
  let e := encodePair er Ratio.encode
  let q := snd er Ratio.encode
  let ps := fst er Ratio.encode
  let times := ratMul.listMapWith 0 0
  let pos := ((constant e Ratio.encode 0).fanout q).comp ratLT
  let body := ite pos (constant e er []) ((q.fanout ps).comp times)
  let powers := (listLength er []).comp Dyadic.program
  exact ((powers.fanout (listFlatten Ratio.encode 0)).comp (body.listFlatMapWith 0 0)).congr _ (fun _ => by
    simp only [Function.comp_apply,guesses,decide_eq_true_eq])

end Scale
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_InstanceDataProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.InstanceProgram
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram
variable (r : ℕ) (hr : 0 < r)
def fractionalInput (I : Nonzero) : FractionalRefinement.Program.Input :=
  ⟨I.val.facilities.card,I.val.clients.card,I.val.k,I.val.computedFractional r hr (I.val.nonzero_clients I.property),
    (I.val.nonzeroFractional_spec I.property r hr).1,card_pos.mpr (I.val.nonzero_clients I.property),
    I.val.indexedDistance,I.val.clientDistance,I.val.facilityDistance,I.val.indexedDistance_nonneg,
    I.val.clientDistance_self,I.val.clientDistance_comm⟩
end MetricKMedian.InstanceProgram
end

end OAI
end


