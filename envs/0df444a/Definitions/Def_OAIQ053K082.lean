-- Prove2me | Definitions.Def_OAIQ053K082
-- name    : OAIQ053K082
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:33:09.092341+00:00
-- url     : https://prove2.me/theorems/3f04ea31-69b6-4a00-864c-f36b23da1bc6
-- title:
--   Definitions bundle OAIQ053K082 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 44 declarations of OpenAI's Lean: 20 definitions, 1 instance and 23 theorems. The definitions and types are `OAI.MetricKMedian.PCP.Compiler.AmplifierProgram.bitsRep`, `OAI.MetricKMedian.PCP.Compiler.AmplifierProgram.co`, `OAI.MetricKMedian.PCP.Compiler.AmplifierProgram.countPoly`, `OAI.MetricKMedian.PCP.Compiler.AmplifierProgram.nextRep`, `OAI.MetricKMedian.PCP.Compiler.AmplifierProgram.sizePoly`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.accept`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.amplified`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.initial`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.inputUnits`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.query`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.represents`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.table`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.tests`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.vars`, `OAI.MetricKMedian.PCP.Compiler.PowerProgram.represents`, `OAI.MetricKMedian.PCP.CookLevin.Test`, `OAI.MetricKMedian.PCP.CookLevin.boundary`, `OAI.MetricKMedian.PCP.CookLevin.space`, `OAI.MetricKMedian.PCP.CookLevin.system`, `OAI.MetricKMedian.PCP.CookLevin.time`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Amplification_AmplifierCompiler`, `KMedian_Amplification_AmplifierGuard`, `KMedian_Amplification_AmplifierIteration`, `KMedian_Amplification_AmplifierProgram`, `KMedian_Amplification_AmplifierTableSize`, `KMedian_Amplification_PowerTable`, `KMedian_CookLevin_CookAmplify`, `KMedian_CookLevin_CookBoundaryProgram`, `KMedian_CookLevin_CookBox`, `KMedian_CookLevin_CookClockProgram`, `KMedian_CookLevin_CookLevin`, `KMedian_CookLevin_CookTable`, `KMedian_Machines_TableCounts`, `KMedian_PCP_UniformProjection`.
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundles `OAIQ053K080` and `OAIQ053K081` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ053K084`; the statements `OAI.MetricKMedian.PCP.Compiler.CookProgram.correct_s53`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.initial_correct_s53` and `OAI.MetricKMedian.PCP.CookLevin.sound_s53`; the proofs of `OAI.MetricKMedian.PCP.Compiler.CookProgram.correct_s53`, `OAI.MetricKMedian.PCP.Compiler.CookProgram.initial_correct_s53` and `OAI.MetricKMedian.PCP.CookLevin.sound_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K080
import Definitions.Def_OAIQ053K081

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PowerTable
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
variable (s : CSPTable A) (h : s.WellFormed) [Nonempty (Fin s.2.length)]
omit [Fintype A] [DecidableEq A] [Inhabited A] in
lemma vertexEquiv_val (v : GlobalRegularization.Node (C s h)) :
    (vertexEquiv s h v).val=vertexCode s h v := rfl
noncomputable def represents (t cap : ℕ) :
    (table t cap s).Represents ((regularCSP s h).powered (cap := cap) t) := by
  have he := CSPTable.grid_build ((regularCSP s h).powered (cap := cap) t)
    (seeds s) (vertexEquiv s h) (Ordered.fixed (Tag (D := Port) t cap))
    (edgeEquiv (G := regularGraph s h) t cap)
    (row RegularProgram.rotate RegularProgram.allowed t cap s) (by
      intro v b
      have hh := row_correct (regularCSP s h) RegularProgram.rotate RegularProgram.allowed
        (vertexCode s h) s (rotate_correct s h) (allowed_correct s h) t cap
        ((edgeEquiv (G := regularGraph s h) t cap) (v,b))
      simpa only [edgeEquiv,Equiv.coe_fn_mk,PortGraph.Walk.ofWord,PortGraph.trace_zero,
        vertexEquiv_val] using hh)
  unfold table
  rw [he]
  exact CSPTable.build_represents _ _ _
end MetricKMedian.PCP.Compiler.PowerProgram

end Inline_PCPPowerTable

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_AmplifierProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAmplifierProgram
namespace MetricKMedian.PCP.Compiler.AmplifierProgram
open Amplifier Binary Binary.Automatic CloudSpec
open scoped Classical

variable (s : CSPTable Label) (h : s.WellFormed) [Nonempty (Fin s.2.length)]
noncomputable def bitsRep : (bits s).Represents
    (FlexibleAmplifier.bits (C s h) (CloudOrder.cloudEmbed (C s h) (EO s)) (padding s h)) :=
  (PowerProgram.represents s h steps radius).relabel (Advice.bitsEquiv Degree (Fin 4) radius)
include h in
lemma bits_wellFormed : (bits s).WellFormed := (bitsRep s h).wellFormed
noncomputable def nextRep : (next s).Represents (AlphabetReduction.paddedBinary
    ((bits s).csp (bits_wellFormed s h))) := AlphabetProgram.represents Bits (bits s) (bits_wellFormed s h)
include h in
lemma next_wellFormed : (next s).WellFormed := by
  let : Nonempty (Fin (bits s).2.length) := Fin.pos_iff_nonempty.mp (bits_wellFormed s h).1
  exact (nextRep s h).wellFormed
end MetricKMedian.PCP.Compiler.AmplifierProgram

end Inline_PCPAmplifierProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_TableCounts
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTableCounts
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

namespace PowerProgram
variable {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
omit [Fintype A] [DecidableEq A] [Inhabited A] in
lemma seeds_upper (s : CSPTable A) (h : s.WellFormed) [Nonempty (Fin s.2.length)] :
    (seeds s).length ≤ (2*ExpanderFamily.growth^2)*s.2.length := by
  have hv := GlobalRegularization.node_upper (CloudSpec.C s h)
  have he := Fintype.card_congr (vertexEquiv s h)
  simp only [Fintype.card_fin] at he hv
  rw [he] at hv
  exact hv
end PowerProgram
end MetricKMedian.PCP.Compiler

end Inline_PCPTableCounts

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_AmplifierTableSize
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAmplifierTableSize
namespace MetricKMedian.PCP.Compiler.AmplifierProgram
open Amplifier Binary Binary.Automatic CloudSpec
open scoped Classical

lemma raw_count (K : Type) [Fintype K] [DecidableEq K] (t cap : ℕ)
    (e : Advice RegularProgram.Port Label cap ≃ BitVector K)
    (s : CSPTable Label) (h : s.WellFormed) [Nonempty (Fin s.2.length)] :
    let out := AlphabetProgram.table K (CSPTable.relabel e (PowerProgram.table t cap s))
    out.1.length+out.2.length ≤ rawCo K t cap*s.2.length := by
  let b := CSPTable.relabel e (PowerProgram.table t cap s)
  have hb1 : b.1.length=(PowerProgram.seeds s).length := rfl
  have hb2 : b.2.length=(PowerProgram.seeds s).length*
      (Ordered.fixed (PowerProgram.Tag (D := RegularProgram.Port) t cap)).entries.length := by
    change ((PowerProgram.table t cap s).2.map _).length=_
    rw [List.length_map]
    exact (PowerProgram.counts t cap s).2
  have hc := AlphabetProgram.counts K b
  exact arithmetic _ _ _ _ _ _ _ _ _ _ _ _ hb1 hb2 hc.1 hc.2 (PowerProgram.seeds_upper s h)
lemma raw_exists (K : Type) [Fintype K] [DecidableEq K] (t cap : ℕ)
    (e : Advice RegularProgram.Port Label cap ≃ BitVector K) :
    ∃ c : ℕ, 0 < c ∧ ∀ (s : CSPTable Label) (_h : s.WellFormed),
      let out := AlphabetProgram.table K (CSPTable.relabel e (PowerProgram.table t cap s))
      out.1.length+out.2.length ≤ c*s.2.length := by
  refine ⟨rawCo K t cap,rawCo_pos K t cap,?_⟩
  intro s h
  let : Nonempty (Fin s.2.length) := Fin.pos_iff_nonempty.mp h.1
  exact raw_count K t cap e s h
lemma coefficient_exists : ∃ c : ℕ, 0 < c ∧ ∀ (s : CSPTable Label) (_h : s.WellFormed),
    (next s).1.length+(next s).2.length ≤ c*s.2.length :=
  raw_exists Bits steps radius (Advice.bitsEquiv Degree (Fin 4) radius)
noncomputable def co : ℕ := coefficient_exists.choose
lemma co_pos : 0 < co := coefficient_exists.choose_spec.1
lemma next_count (s : CSPTable Label) (h : s.WellFormed) :
    (next s).1.length+(next s).2.length ≤ co*s.2.length :=
  coefficient_exists.choose_spec.2 s h
end MetricKMedian.PCP.Compiler.AmplifierProgram

end Inline_PCPAmplifierTableSize

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_AmplifierIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAmplifierIteration
namespace MetricKMedian.PCP.Compiler.AmplifierProgram
open Amplifier Binary Binary.Automatic
open scoped Classical

lemma iterate_valid {s : CSPTable Label} (h : s.WellFormed) (n : ℕ) : (iterate n s).WellFormed := by
  induction n with
  | zero => exact h
  | succ n ih =>
    let : Nonempty (Fin (iterate n s).2.length) := Fin.pos_iff_nonempty.mp ih.1
    exact next_wellFormed (iterate n s) ih
lemma iterate_count {s : CSPTable Label} (h : s.WellFormed) (n : ℕ) :
    (iterate n s).1.length+(iterate n s).2.length ≤ co^n*(s.1.length+s.2.length) := by
  induction n with
  | zero => simp only [iterate,pow_zero,one_mul,le_refl]
  | succ n ih =>
    have hh := iterate_valid h n
    let : Nonempty (Fin (iterate n s).2.length) := Fin.pos_iff_nonempty.mp hh.1
    have hi : (iterate n s).2.length ≤ co^n*(s.1.length+s.2.length) := (Nat.le_add_left _ _).trans ih
    calc
      _ ≤ co*(iterate n s).2.length := next_count _ hh
      _ ≤ co*(co^n*(s.1.length+s.2.length)) := Nat.mul_le_mul_left _ hi
      _ = _ := by rw [pow_succ']; exact (Nat.mul_assoc _ _ _).symm
end MetricKMedian.PCP.Compiler.AmplifierProgram

end Inline_PCPAmplifierIteration

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_AmplifierGuard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAmplifierGuard
namespace MetricKMedian.PCP.Compiler.AmplifierProgram
open Amplifier Binary Binary.Automatic
open scoped Classical

lemma schedule_valid (s : CSPTable Label) (h : s.WellFormed) (i : ℕ) :
    (schedule s i).2.2.WellFormed := iterate_valid h _
lemma schedule_count (s : CSPTable Label) (h : s.WellFormed) (i : ℕ) :
    (schedule s i).2.2.1.length+(schedule s i).2.2.2.length≤
      co*(s.2.length^co*(s.1.length+s.2.length)) := by
  have hc : 1 ≤ co := co_pos
  apply (iterate_count h _).trans
  have hpow := Nat.pow_le_pow_right hc (min_le_right i (Nat.log 2 s.2.length+1))
  have hb := log_power_bound co s.2.length h.1
  calc
    _ ≤ co^(Nat.log 2 s.2.length+1)*(s.1.length+s.2.length) := Nat.mul_le_mul_right _ hpow
    _ = co*(co^(Nat.log 2 s.2.length)*(s.1.length+s.2.length)) := by rw [pow_succ',Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hb)
lemma generate_valid (s : CSPTable Label) : (generate s).WellFormed := by
  rw [generate_eq]
  exact iterate_valid (normalize_valid s) _
end MetricKMedian.PCP.Compiler.AmplifierProgram

end Inline_PCPAmplifierGuard

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_AmplifierCompiler
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.Compiler.LocalCompiler.assignmentSetCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAmplifierCompiler
namespace MetricKMedian.PCP.Compiler.AmplifierProgram
open Amplifier Binary Binary.Automatic Polynomial
open scoped Classical

noncomputable def countPoly : Polynomial ℕ := C co*((X+2)^co*(X+2))
noncomputable def sizePoly : Polynomial ℕ :=
  2*(X+3)+1+(2*(2*(X+2)+1)+1+
    (2*(countPoly*C (2*(enc ()).length+1))+1+
      countPoly*(2*(2*(countPoly+1)+1+(2*(countPoly+1)+1+C (CSPTable.relationBound (A := Label))))+1)))
lemma reachable_size (s : CSPTable Label) (i : ℕ) :
    (enc (guarded^[i] ((normalize s).2.length,(1,normalize s)))).length ≤ sizePoly.eval (enc s).length := by
  rw [guarded_iterate _ (normalize_valid s)]
  have hn := normalize_count s
  have he : (normalize s).2.length≤(enc s).length+2 := by omega
  have hc := schedule_count (normalize s) (normalize_valid s) i
  have hc' : (schedule (normalize s) i).2.2.1.length+(schedule (normalize s) i).2.2.2.length ≤
      countPoly.eval (enc s).length := by
    apply hc.trans
    unfold countPoly
    simp only [eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_ofNat]
    gcongr
  have ht := CSPTable.size_bound (schedule_valid (normalize s) (normalize_valid s) i) _ hc'
  have hb : (normalize s).2.length.bits.length ≤ (enc s).length+3 :=
    (NatBinary.length_le_height Nat.lt_two_pow_self.le).trans (by omega)
  have hh : (schedule (normalize s) i).2.1.bits.length ≤ 2*((enc s).length+2)+1 := by
    apply (NatBinary.length_le_height Nat.lt_two_pow_self.le).trans
    have hh := schedule_counter (normalize s) (normalize_valid s) i
    omega
  change (encodePair Nat.bits (encodePair Nat.bits enc) _).length≤_
  rw [encodePair_length,encodePair_length]
  change 2*(normalize s).2.length.bits.length+1+(2*(schedule (normalize s) i).2.1.bits.length+1+
    (enc (schedule (normalize s) i).2.2).length)≤_
  apply (Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left _ hb) _)
    (Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left _ hh) _) ht)).trans
  unfold CSPTable.sizeBound sizePoly
  simp only [eval_add,eval_mul,eval_C,eval_X,eval_one,eval_ofNat]
  omega
lemma poly_trajectory : Poly (fun s : CSPTable Label =>
    Iteration.iterates guarded ((normalize s).2.length,(1,normalize s)) ((normalize s).2.length+2)) := by
  refine ⟨poly_guarded.program.iteratesFrom poly_initialState.program poly_steps.program
    (0,(1,fallback)) (X+4) sizePoly ?_ ?_⟩
  · intro s
    have hn := normalize_count s
    simp only [eval_add,eval_X,eval_ofNat]
    omega
  · intro s i hi
    exact reachable_size s i
lemma poly_generate : Poly generate := by
  have hi : Poly (fun s : CSPTable Label => (normalize s).2.length+1) :=
    Poly.nat_add.comp (Poly.pair (Poly.list_length.comp (Poly.snd.comp poly_normalize)) (Automatic.Poly.const _))
  have hg := Poly.list_getD_comp (0,(1,fallback)) poly_trajectory hi
  apply poly_congr (Poly.snd.comp (Poly.snd.comp hg))
  intro s
  change ((Iteration.iterates guarded ((normalize s).2.length,(1,normalize s)) ((normalize s).2.length+2))[(normalize s).2.length+1]?.getD
    (0,(1,fallback))).2.2=generate s
  rw [Iteration.iterates_eq]
  simp only [List.getElem?_map,List.getElem?_range,show (normalize s).2.length+1<(normalize s).2.length+2 by omega,
    Option.map_some,Option.getD_some,generate]
end MetricKMedian.PCP.Compiler.AmplifierProgram

end Inline_PCPAmplifierCompiler

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_CookLevin
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.inputSymbolInhabited _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.outputSymbolInhabited _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.symbolCoding _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.symbolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.tapeCoding _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.tapeHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCookLevin

namespace MetricKMedian.PCP.CookLevin
open Turing Turing.TM2 Function Finset
open Complexity Tableau
open scoped Classical

variable {verify : Word × Word → Bool}
variable (P : TM2ComputableInPolyTime encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀ k, Fintype (P.tm.Γ k)]
attribute [local instance] OAI.MetricKMedian.PCP.CookLevin.instFintypeKTmBool_solutions
attribute [local instance] OAI.MetricKMedian.PCP.CookLevin.instFintypeΛTmBool_solutions
attribute [local instance] OAI.MetricKMedian.PCP.CookLevin.instFintypeσTmBool_solutions
def time (x : Word) : ℕ := P.time.eval (inputSize p x)
noncomputable def space (x : Word) : ℕ := inputSize p x+radius P.tm.m*time P p x+1
noncomputable def boundary (x : Word) : Boundary (Γ := P.tm.Γ) (Λ := P.tm.Λ) (σ := P.tm.σ) where
  firstControl := (some P.tm.main,P.tm.initialState)
  firstPrefix := (initList P.tm (inputPrefix P x)).stk
  certificateBound k := if k=P.tm.k₀ then p.eval x.length else 0
  last := haltList P.tm [P.outputAlphabet.invFun true]
noncomputable def system (x : Word) := boundedSystem P.tm.m (boundary P p x) (time P p x) (space P p x)

end MetricKMedian.PCP.CookLevin

end Inline_PCPCookLevin

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_CookClockProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.inputSymbolInhabited _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.outputSymbolInhabited _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.symbolCoding _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.symbolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.tapeCoding _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.tapeHardcoded _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCookClockProgram
namespace MetricKMedian.PCP.Compiler.CookProgram
open Binary Binary.Automatic CookLevin Complexity Tableau
open scoped Classical

variable {verify : Word×Word→Bool}
variable (P : Turing.TM2ComputableInPolyTime Complexity.encodePair encodeBit verify) (p : Polynomial ℕ)
local instance instFintypeKTmBool_solutions_r150ddb_1 : Fintype P.tm.K := P.tm.kFin
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeΛTmBool_solutions
local instance instFintypeσTmBool_solutions_r150ddb_1 : Fintype P.tm.σ := P.tm.σFin
noncomputable def inputUnits (x : Word) : List Unit := List.replicate (inputSize p x) ()
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPCookClockProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_CookBox
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.inputSymbolInhabited _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.outputSymbolInhabited _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.symbolCoding _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.symbolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.tapeCoding _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.tapeHardcoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCookBox

namespace MetricKMedian.PCP.CookLevin
open Turing Turing.TM2 Function Finset
open Complexity Tableau
open scoped Classical

variable {verify : Word × Word → Bool}
variable (P : TM2ComputableInPolyTime encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀ k, Fintype (P.tm.Γ k)]
local instance instFintypeKTmBool_solutions_1_r150ddb_1 : Fintype P.tm.K := P.tm.kFin
attribute [local instance] OAI.MetricKMedian.PCP.CookLevin.instFintypeΛTmBool_solutions_1
local instance instFintypeσTmBool_solutions_1_r150ddb_1 : Fintype P.tm.σ := P.tm.σFin
abbrev Test (x : Word) := Clause (K := P.tm.K) (time P p x) (space P p x) ⊕ BoundaryClause (K := P.tm.K) (space P p x)
noncomputable instance testNonempty (x : Word) : Nonempty (Test P p x) :=
  ⟨Sum.inr (false,Sum.inl ())⟩
end MetricKMedian.PCP.CookLevin

end Inline_PCPCookBox

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_CookBoundaryProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCookBoundaryProgram
namespace MetricKMedian.PCP.Compiler.CookProgram
open Binary Binary.Automatic CookLevin Complexity Tableau TableauDirectory FiniteList Turing Turing.TM2
open scoped Classical

variable {verify : Word×Word→Bool}
variable (P : Turing.TM2ComputableInPolyTime Complexity.encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀k,Fintype (P.tm.Γ k)]
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeKTmBool_solutions_1
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeΛTmBool_solutions_1
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeσTmBool_solutions_1
lemma poly_inputPrefix : Poly (inputPrefix P) := by
  exact Poly.list_map ((hardcoded P.inputAlphabet.invFun).comp Poly.snd) poly_firstWord
lemma poly_firstCell_fixed (k : P.tm.K) :
    Poly (fun z : Word×ℕ=>firstCellSet P.tm.m (boundary P p z.1) k z.2) := by
  by_cases hk : k=P.tm.k₀
  · subst k
    have hh := FiniteList.poly_prefixFilter (inputPrefix P) (fun x:Word=>p.eval x.length)
      (fun a : Query P.tm.m→Value P.tm.m => (a (q0 P.tm.m)).2.2 P.tm.k₀) (poly_inputPrefix P) (poly_certificateBound p)
    apply poly_congr hh
    intro z
    ext a
    simp [firstCellSet,boundary,initList]
  · apply poly_congr (Automatic.Poly.const (Finset.univ.filter (fun a : Query P.tm.m→Value P.tm.m => (a (q0 P.tm.m)).2.2 k=none)))
    intro z
    ext a
    simp [firstCellSet,boundary,initList,hk,prefixCell]
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPCookBoundaryProgram

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_CookTable
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCookTable
namespace MetricKMedian.PCP.Compiler.CookProgram
open Binary Binary.Automatic CookLevin Complexity Tableau TableauDirectory
open scoped Classical

variable {verify : Word×Word→Bool}
variable (P : Turing.TM2ComputableInPolyTime Complexity.encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀k,Fintype (P.tm.Γ k)]
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeKTmBool_solutions_2
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeΛTmBool_solutions_2
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeσTmBool_solutions_2
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instInhabitedKTmBool_solutions
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instInhabitedValueKTmBoolΓΛσM
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instInhabitedQueryKTmBoolΓΛσM
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instDecidableEqQueryKTmBoolΓΛσM
noncomputable def vars (x : Word) := TableauDirectory.vars P.tm.k₀ (time P p x) (space P p x)
noncomputable def tests (x : Word) := TableauDirectory.tests P.tm.k₀ (time P p x) (space P p x)
noncomputable def query (x : Word) := rawQuery P.tm.m P.tm.k₀ (time P p x) (space P p x)
noncomputable def accept (x : Word) := rawAccept P.tm.m (boundary P p x)
noncomputable def table (x : Word) := LocalCompiler.table (vars P p) (tests P p) (query P p) (accept P p) x
noncomputable def represents (x : Word) : (table P p x).Represents (system P p x).binary := by
  exact LocalCompiler.represents (vars P p) (tests P p) (query P p) (accept P p)
    (system P p x) (varOrder (K:=P.tm.K) (time P p x) (space P p x))
    (testOrder (K:=P.tm.K) (time P p x) (space P p x))
    (varCode P.tm.k₀) (testCode P.tm.k₀)
    (varCode_injective _ _ _) (testCode_injective _ _ _) x
    (vars_correct _ _ _) (tests_correct _ _ _)
    (rawQuery_correct _ _ _ _ _) (rawAccept_correct _ _ _ _ _)
lemma wellFormed (x : Word) : (table P p x).WellFormed := (represents P p x).wellFormed
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPCookTable

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_CookLevin_CookAmplify
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCookAmplify
namespace MetricKMedian.PCP.Compiler.CookProgram
open Binary Binary.Automatic CookLevin Complexity Tableau Amplifier
open scoped Classical

variable {verify : Word×Word→Bool}
variable (P : Turing.TM2ComputableInPolyTime Complexity.encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀k,Fintype (P.tm.Γ k)]
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeKTmBool_solutions_3
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeΛTmBool_solutions_3
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeσTmBool_solutions_3
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instDecidableEqQueryKTmBoolΓΛσM_1
noncomputable def initial (x : Word) : CSPTable Label := InitialProgram.table (FiniteCSP.Label (Q:=Query P.tm.m) (A:=Value P.tm.m)) (table P p x)
lemma initial_valid (x : Word) : (initial P p x).WellFormed :=
  InitialProgram.valid (FiniteCSP.Label (Q:=Query P.tm.m) (A:=Value P.tm.m)) (table P p x) (wellFormed P p x)
noncomputable def amplified (x : Word) : CSPTable Label := AmplifierProgram.generate (initial P p x)
lemma amplified_valid (x : Word) : (amplified P p x).WellFormed := AmplifierProgram.generate_valid _
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPCookAmplify

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_UniformProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPUniformProjection
namespace MetricKMedian.PCP.Compiler.CookProgram
open Binary Binary.Automatic CookLevin Complexity Tableau Amplifier
open scoped Classical

variable {verify : Word×Word→Bool}
variable (P : Turing.TM2ComputableInPolyTime Complexity.encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀k,Fintype (P.tm.Γ k)]
local instance instFintypeKTmBool_solutions_4_r150ddb_1 : Fintype P.tm.K := P.tm.kFin
local instance instFintypeΛTmBool_solutions_4_r150ddb_1 : Fintype P.tm.Λ := P.tm.ΛFin
local instance instFintypeσTmBool_solutions_4_r150ddb_1 : Fintype P.tm.σ := P.tm.σFin
noncomputable local instance instDecidableEqQueryKTmBoolΓΛσM_2_r150ddb_1 : DecidableEq (Query P.tm.m) := Classical.decEq _
local instance instNonemptyFinLengthCSPRowLabelSndListUnitAmplified (x : Word) : Nonempty (Fin (amplified P p x).2.length) :=
  Fin.pos_iff_nonempty.mp (amplified_valid P p x).1
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPUniformProjection

end OAI
end


