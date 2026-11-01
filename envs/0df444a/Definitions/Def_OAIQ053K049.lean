-- Prove2me | Definitions.Def_OAIQ053K049
-- name    : OAIQ053K049
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:07:56.376864+00:00
-- url     : https://prove2.me/theorems/90afc55f-5a23-47d7-bce8-4421b755d93f
-- title:
--   Definitions bundle OAIQ053K049 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 69 declarations of OpenAI's Lean: 27 definitions, 1 inductive type or structure and 41 theorems. The definitions and types are `OAI.MetricKMedian.Complexity.firstWord`, `OAI.MetricKMedian.Coverage.Raw.indices`, `OAI.MetricKMedian.Coverage.Raw.parse`, `OAI.MetricKMedian.InputParser.natRead`, `OAI.MetricKMedian.InputParser.ratRead`, `OAI.MetricKMedian.LPBinary.Nearest.amountProgram`, `OAI.MetricKMedian.LPBinary.Nearest.fillingProgram`, `OAI.MetricKMedian.LPBinary.Nearest.priorProgram`, `OAI.MetricKMedian.Preparation.FractionalRefinement.ScanProgram.Input`, `OAI.MetricKMedian.Preparation.FractionalRefinement.scan`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Data.law`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Data.scan`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Data.tables`, `OAI.MetricKMedian.Preparation.RationalUnitInput.scan`, `OAI.MetricKMedian.SparseBernoulli.ListOperation.endpoint`, `OAI.MetricKMedian.SparseBernoulli.ListOperation.featureList`, `OAI.MetricKMedian.SparseBernoulli.ListOperation.tests`, `OAI.MetricKMedian.SparseBernoulli.ListOperation.value`, `OAI.MetricKMedian.SparseIntegerLaw.BinarySparse.ed`, `OAI.MetricKMedian.SparseOuterLaw.law`, `OAI.MetricKMedian.SparsePrepared.law`, `OAI.MetricKMedian.SparseSignedPreparation.law`, `OAI.MetricKMedian.Taper.ListOperation.AllRaw`, `OAI.MetricKMedian.Taper.ListOperation.colocated`, `OAI.MetricKMedian.Taper.ListOperation.extras`, `OAI.MetricKMedian.Taper.ListOperation.sourceRow`, `OAI.MetricKMedian.Taper.ListOperation.zeroRow`, `OAI.MetricKMedian.TaperGraphProgram.rawQ`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Binary_NumericParserProgram`, `KMedian_Geometry_RationalFractionalScan`, `KMedian_Geometry_RationalUnitScan`, `KMedian_Hardness_Classes`, `KMedian_Hardness_Encoding`, `KMedian_Optimization_FractionalScanProgram`, `KMedian_Preparation_RationalSupplierScan`, `KMedian_Probability_BernoulliListOperations`, `KMedian_Process_TaperAllProgram`, `KMedian_Process_TaperGraphProgram`, `KMedian_Process_TaperListProgram`, `KMedian_Programs_NearestListProgram`, `KMedian_Rounding_RationalSignedTerminal`, `KMedian_Sparse_SparseBernoulliSubsets`, `KMedian_Sparse_SparseBernoulliSupport`, `KMedian_Sparse_SparseBind`, `KMedian_Sparse_SparseBindProgram`, `KMedian_Sparse_SparseListTrim`, `KMedian_Sparse_SparseOuterLaw`, `KMedian_Sparse_SparsePreparedLaw`, `KMedian_Sparse_SparseProductProgram`, `KMedian_Sparse_SparseSignedPartial`, `KMedian_Sparse_SparseSignedPreparation`, `KMedian_Sparse_SparseSignedRounding`.
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundles `OAIQ053K044`, `OAIQ053K045` and `OAIQ053K046` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K054`, `OAIQ053K055`, `OAIQ053K056`, `OAIQ053K057`, `OAIQ053K058`, `OAIQ053K060` and `OAIQ053K061`; the statement `OAI.MetricKMedian.Preparation.RationalBundles.scan_geometry_s53`; the proofs of `OAI.MetricKMedian.SparseBernoulli.conditional_count_tail_s53`, `OAI.MetricKMedian.SparseBernoulli.count_variance_s53`, `OAI.MetricKMedian.SparseEnumeratedBatch.erasure_lower_s53`, `OAI.MetricKMedian.SparseEnumeratedBatch.marginal_error_s53`, `OAI.MetricKMedian.SparseEnumeratedBatch.marginal_le_s53` and `OAI.MetricKMedian.SparseEnumeratedBatch.relevant_generator_estimate_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K044
import Definitions.Def_OAIQ053K045
import Definitions.Def_OAIQ053K046

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_NumericParserProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.InputParser
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
@[fun_prop] theorem take_poly {α : Type} [Coding α] [Inhabited α] : Poly (fun x : List α × ℕ => x.1.take x.2) := ⟨listTake enc default⟩
@[fun_prop] theorem drop_poly {α : Type} [Coding α] [Inhabited α] : Poly (fun x : List α × ℕ => x.1.drop x.2) := ⟨listDrop enc default⟩
@[fun_prop] theorem value_poly : Poly Word.value := ⟨BooleanLists.valueProgram⟩
@[fun_prop] theorem signed_poly : Poly (fun x : Bool × ℕ => Signed.value x.1 x.2) := ⟨intFromParts⟩
@[fun_prop] theorem mkRat_poly : Poly (fun x : ℤ × ℕ => mkRat x.1 x.2) := ⟨mkRational⟩
@[fun_prop] theorem width_poly : Poly width := by unfold width; apply list_findIdx <;> fun_prop
def natRead (xs : List Bool) : ℕ × List Bool :=
  (Word.value ((xs.drop (width xs+1)).take (width xs)),xs.drop (width xs+1+width xs))
@[fun_prop] theorem natRead_poly : Poly natRead := by
  have hd : Poly (fun xs : List Bool => xs.drop (width xs+1)) :=
    Poly.comp (f:=fun x : List Bool × ℕ => x.1.drop x.2) drop_poly (g:=fun xs : List Bool => (xs,width xs+1)) (by fun_prop)
  have ht : Poly (fun xs : List Bool => (xs.drop (width xs+1)).take (width xs)) :=
    Poly.comp (f:=fun x : List Bool × ℕ => x.1.take x.2) take_poly (pair hd width_poly)
  exact pair (Poly.comp value_poly ht) (Poly.comp (f:=fun x : List Bool × ℕ => x.1.drop x.2) drop_poly (g:=fun xs : List Bool => (xs,width xs+1+width xs)) (by fun_prop))
 theorem prefix_width (n : ℕ) (xs : List Bool) : width (List.replicate n true++false::xs)=n := by
  induction n with
  | zero => simp [width,List.findIdx_cons]
  | succ n ih => simp only [List.replicate_succ,List.cons_append,width,List.findIdx_cons,Bool.not_true,Bool.false_eq_true,↓reduceIte]; exact congrArg Nat.succ ih
 theorem natRead_append (n : ℕ) (xs : List Bool) : natRead (encodeNat n++xs)=(n,xs) := by
  unfold natRead
  have hw : width (encodeNat n++xs)=n.bits.length := by
    simpa only [encodeNat,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using prefix_width n.bits.length (n.bits++xs)
  rw [hw]
  have hd : (encodeNat n++xs).drop (n.bits.length+1)=n.bits++xs := by
    simp [encodeNat,List.drop_append,List.append_assoc]
  rw [hd,show (encodeNat n++xs).drop (n.bits.length+1+n.bits.length)=xs from by
    rw [← List.drop_drop,hd,List.drop_left]]
  simp only [List.take_left,Word.value_bits]
def ratRead (xs : List Bool) : ℚ × List Bool :=
  let a := natRead xs.tail
  let b := natRead a.2
  (mkRat (Signed.value (xs.head?.getD false) a.1) b.1,b.2)
@[fun_prop] theorem ratRead_poly : Poly ratRead := by unfold ratRead; fun_prop
end MetricKMedian.InputParser
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBernoulliSubsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

theorem subset_moment (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset (Fin n)) (hS : S.card ≤ d) :
    (run (d := d) p hp n).moment (fun q => ∏ i ∈ S, flag q i)=∏ i ∈ S, p i := by
  have hh := (run_spec (d := d) p hp).2 (tuple S)
  simpa only [monomial,used_tuple S hS] using hh

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBind
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

theorem bindCompress_spec {d : ℕ} (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (v : β → Fin d → ℚ) :
    let ν := μ.bindCompress κ v
    ν.length ≤ d+1 ∧
    (∀ i : Fin ν.length, ∃ a : Fin μ.length, ∃ b : Fin (κ a).length,
      ν.states[i.val]=(κ a).states[b.val]) ∧
    ∀ j, ν.moment (fun z => v z j)=
      ∑ a, μ.law.rational.weight a*(κ a).moment (fun z => v z j) := by
  have h := (μ.bindIndexed κ).compressAuto_correct v
  refine ⟨h.1,?_,fun j => (h.2.2 j).trans (bindIndexed_moment μ κ _)⟩
  intro i
  obtain ⟨b,hb⟩ := h.2.1 i
  let z := (finSigmaFinEquiv (n := fun a => (κ a).length)).symm b
  refine ⟨z.1,z.2,?_⟩
  exact hb.trans (by
    simp only [bindIndexed,Vector.getElem_ofFn]
    congr 3)

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBernoulliSupport
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.RationalSignedTerminal.point_state _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

theorem single_moment (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (i : Fin n) : (run (d := 2) p hp n).moment (fun q => flag q i)=p i := by
  simpa only [prod_singleton] using subset_moment p hp {i} (by simp : ({i} : Finset (Fin n)).card ≤ 2)

theorem fixed (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (a : Fin (run (d := 2) p hp n).length) (i : Fin n) (hi : p i=0 ∨ p i=1) :
    flag (run (d := 2) p hp n).states[a.val] i=p i := by
  have hm := single_moment p hp i
  rcases hi with hi | hi
  · have hh := (run (d := 2) p hp n).zero_indicator (fun q => q i=true)
      (hm.trans hi) a (run_positive p hp n a)
    simp only [flag,ite_eq_right hh,hi]
  · have hh := (run (d := 2) p hp n).one_indicator (fun q => q i=true)
      (hm.trans hi) a (run_positive p hp n a)
    simp only [flag,ite_eq_left hh,hi]

end MetricKMedian.SparseBernoulli
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalSignedTerminal
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalSignedTerminal
open Finset RationalWeightedStep RationalSignedStep
variable {n : ℕ}

theorem terminal_spec (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1)
    (hu : ∀ i, 0 < u i → u i ≤ 1) (hpair : ¬Active u p)
    (a : Fin (terminal u p hp).length) :
    let q := (terminal u p hp).states[a.val]
    (∀ i, 0 ≤ point q i ∧ point q i ≤ 1) ∧ (fractional q).card ≤ 1 ∧
    (∑ i, u i*point q i) ≤ (∑ i, u i*point p i)+1 := by
  dsimp only
  change Fin (SparseBernoulli.run (d := 2) (point p) hp n).length at a
  have he := SparseIntegerLaw.map_states (SparseBernoulli.run (d := 2) (point p) hp n) (state u p) a
  change (terminal u p hp).states[a.val]=_ at he
  rw [he]
  apply state_spec u p hp hu hpair
  intro i hi
  apply SparseBernoulli.fixed _ hp a i
  have hr := MarginalRounding.nonfractional_integral
    (fun i => by change 0 ≤ (point p i : ℝ); exact_mod_cast (hp i).1 : ∀ i, 0 ≤ realPoint p i)
    (fun i => by change (point p i : ℝ) ≤ 1; exact_mod_cast (hp i).2 : ∀ i, realPoint p i ≤ 1)
    (show i ∉ MarginalRounding.fractional (realPoint p) by simpa only [real_fractional] using hi)
  change (point p i : ℝ)=0 ∨ (point p i : ℝ)=1 at hr
  exact_mod_cast hr

end MetricKMedian.RationalSignedTerminal
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSignedPartial
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedPartial
open Finset RationalSignedStep
open RationalWeightedStep (point fractional)
open SparseWeightedPartial (features features_single features_pair)
variable {n : ℕ}

theorem run_terminal (β : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (a : Fin (run β p n).length) :
    ¬Active β (run β p n).states[a.val] := by
  rcases (run_invariants β p hp n a).2.2 with h | h
  · intro ha
    have hi := (pair β (run β p n).states[a.val] ha).property.1
    have hc := card_pos.mpr ⟨_,hi⟩
    omega
  · exact h

end MetricKMedian.SparseSignedPartial
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSignedRounding
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedRounding
open Finset
open RationalWeightedStep (point fractional)
open SparseWeightedPartial (features features_single features_pair)
variable {n : ℕ}

theorem round_invariants (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (hu : ∀ i, 0 < u i → u i ≤ 1)
    (a : Fin (round u p hp).length) :
    let q := (round u p hp).states[a.val]
    (∀ i, 0 ≤ point q i ∧ point q i ≤ 1) ∧ (fractional q).card ≤ 1 ∧
    (∑ i, u i*point q i) ≤ (∑ i, u i*point p i)+1 := by
  obtain ⟨b,c,hbc⟩ := ((SparseSignedPartial.run u p n).bindCompress_spec
    (kernel u p hp) features).2.1 a
  dsimp only
  change (round u p hp).states[a.val]=_ at hbc
  rw [hbc]
  have hh := RationalSignedTerminal.terminal_spec u (SparseSignedPartial.run u p n).states[b.val]
    (SparseSignedPartial.run_invariants u p hp n b).1 hu
    (SparseSignedPartial.run_terminal u p hp b) c
  dsimp only at hh
  exact ⟨hh.1,hh.2.1,hh.2.2.trans_eq
    (congrArg (fun z : ℚ => z+1) (SparseSignedPartial.run_invariants u p hp n b).2.1)⟩

end MetricKMedian.SparseSignedRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSignedPreparation
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

def law (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (p : Vector ℚ m)
    (hp : ∀ e, 0 ≤ point p e ∧ point p e ≤ 1) (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) :
    SparseIntegerLaw (State n m) :=
  let μ := SparseSignedRounding.round (signed D c) p hp
  μ.bindIndexed (fun a => kernel D μ.states[a.val]
    (SparseSignedRounding.round_invariants (signed D c) p hp (fun e _ =>
      (sub_le_self _ (Nat.cast_nonneg _)).trans (hc e).2) a).1)

end MetricKMedian.SparseSignedPreparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseOuterLaw
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

abbrev law (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) : SparseIntegerLaw (State n m) :=
  SparseSignedPreparation.law D c (fraction q) (SparseGridRounding.fraction_unit q hq) hc

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparsePreparedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw
open SparseSignedPreparation (State)
variable {n m f : ℕ}

def law (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (Δ : ℕ)
    (P : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (p : Fin n → ℚ)
    (hc : ∀ e,0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e,0 ≤ q e) :
    SparseIntegerLaw (State n m × SparseCounts.Table f n) :=
  (SparseOuterLaw.law D c q hc hq).bindIndexed
    (fun a => kernel D q Δ P y p (SparseOuterLaw.law D c q hc hq).states[a.val])

end MetricKMedian.SparsePrepared
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RationalSupplierScan
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars

namespace Data
variable {f n j : ℕ} {τ : ℝ} (D : Data f n) (qR : FixedBatch.RationalParameters τ)

def law := SparsePrepared.law (RationalSuppliers.D D.A) a
  (q D.y D.P D.A D.c D.γ qR.g) qR.Δ D.P D.y D.p a_bounds
  (q_nonneg D.y D.P D.A D.c D.γ qR.g D.hy D.hc0 D.hγ.le (FixedParameters.positive qR).le)

def tables : List (Fin (f+n*f) → ℕ) :=
  (D.law qR).states.toList.map (counts D.y D.P D.A D.c D.γ qR.g)

def scan (df : Fin f → Fin f → ℚ) (dc : Fin j → Fin f → ℚ) (B : ℚ) :=
  qR.roundList df dc (original (f:=f) (n:=n)) (D.tables qR) B

end Data
end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalUnitScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Preparation.RationalUnitInput
open Finset
variable {f j : ℕ} {X : Type} [PseudoMetricSpace X]
variable (U : RationalUnitInput f j) (R : U.Realization X) {η τ : ℝ} (p : RationalAllParameters η τ)

def scan (B : ℚ) : Option (Finset (Fin f)) := (U.suppliers R p).scan p.round U.df U.dc B

end MetricKMedian.Preparation.RationalUnitInput
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalFractionalScan
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.FractionalRefinement
open Finset
variable {f j : ℕ} {X : Type} [PseudoMetricSpace X]
variable (a : TruncatedLP.FractionalData f j) (k : ℕ) (ha : a.Valid k) (hj : 0<j)
    (dc : Fin j → Fin f → ℚ) (dd : Fin j → Fin j → ℚ) (df : Fin f → Fin f → ℚ)
    (hdc : ∀ c i, 0≤dc c i) (hdd : ∀ c, dd c c=0) (hds : ∀ c c', dd c c'=dd c' c)
    (i : Fin f → X) (client : Fin j → X)
    (hdf : ∀ b b', dist (i b) (i b')=(df b b':ℝ))
    (hc : ∀ c b, dist (client c) (i b)=(dc c b:ℝ))
    (hcc : ∀ c c', dist (client c) (client c')=(dd c c':ℝ))
    {η τ : ℝ} (p : RationalAllParameters η τ)

def scan (B : ℚ) : Option (Finset (Fin f)) :=
  let U := unitInput a k ha hj dc dd df hdc hdd hds
  let R := realization a k ha hj dc dd df hdc hdd hds i client hdf hc hcc
  (U.scan R p B).map (fun O => O.image (original a k ha hj dc))

end MetricKMedian.Preparation.FractionalRefinement
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_NearestListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset

namespace Nearest
noncomputable def priorProgram : PolyProgram (encodePair ees ee) Ratio.encode (fun x : List Entry × Entry => prior x.1 x.2) := by
  let pred := (exchange ee ee).comp beforeProgram
  let filtered := (exchange ees ee).comp (pred.listFilterWith (0,(0,0)) (0,(0,0)))
  let cap := (snd Nat.bits (encodePair Ratio.encode Ratio.encode)).comp (fst Ratio.encode Ratio.encode)
  exact ((filtered.comp (cap.listMap (0,(0,0)))).comp ratSum).congr _ (fun _ => rfl)
noncomputable def amountProgram : PolyProgram (encodePair ees ee) Ratio.encode (fun x : List Entry × Entry => amount x.1 x.2) := by
  let cap := ((snd ees ee).comp (snd Nat.bits (encodePair Ratio.encode Ratio.encode))).comp (fst Ratio.encode Ratio.encode)
  let remain := ((constant (encodePair ees ee) Ratio.encode 1).fanout priorProgram).comp ratSub
  exact ((cap.fanout (remain.comp Program.positivePart)).comp Program.ratMin).congr _ (fun _ => rfl)
noncomputable def fillingProgram : PolyProgram (encodePair er er) er (fun x : Row × Row => filling x.1 x.2) :=
  ((entriesProgram.fanout entriesProgram).comp (amountProgram.listMapWith (0,(0,0)) 0)).congr _ (fun _ => rfl)
end Nearest
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseListTrim
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.PolyProgram Function Finset
variable {α : Type}
abbrev ed (ea : α → List Bool) := encodePair el (encodeList ea)

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_TaperListProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Taper.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly Finset

@[fun_prop] theorem upper_poly : Poly upper := by
  unfold upper
  have h : Poly (fun ds : Row => ds.map (fun q => 1/q)) := by apply list_map <;> fun_prop
  fun_prop
@[fun_prop] theorem breaks_poly : Poly breaks := by
  unfold breaks
  have h : Poly (fun x : ℚ × Row => x.2.map (fun q => (1-x.1)/q)) := by apply list_map <;> fun_prop
  have h' : Poly (fun x : ℚ × Row => x.2.map (fun q => 1/q)) := by apply list_map <;> fun_prop
  fun_prop
@[fun_prop] theorem aSum_poly : Poly aSum := by
  unfold aSum
  apply comp rat_sum
  apply list_map
  · unfold aCoef; fun_prop
  · fun_prop
@[fun_prop] theorem bSum_poly : Poly bSum := by
  unfold bSum
  apply comp rat_sum
  apply list_map
  · unfold bCoef; fun_prop
  · fun_prop
@[fun_prop] theorem candidateList_poly : Poly candidateList := by
  unfold candidateList
  dsimp only
  apply comp (f:=fun x : Row × Row => x.1++x.2) (g:=fun x : Raw => (breaks (x.1.2,x.2), (breaks (x.1.2,x.2)).flatMap (fun a => (breaks (x.1.2,x.2)).map (fun b => (aSum ((x.1.2,x.2),(a+b)/2)-1/x.1.1)/bSum ((x.1.2,x.2),(a+b)/2))))) list_append
  apply pair
  · fun_prop
  · apply list_flatMap
    · apply list_map <;> fun_prop
    · fun_prop
@[fun_prop] theorem mass_poly : Poly mass := by
  unfold mass
  apply comp rat_sum
  apply list_map
  · unfold rationalMarginal; fun_prop
  · fun_prop
@[fun_prop] theorem roots_poly : Poly roots := by
  unfold roots
  apply list_filter <;> fun_prop
@[fun_prop] theorem radius_poly : Poly radius := by
  exact comp (f:=fun x : Row × ℚ => x.1.foldl max x.2) (g:=fun x : Raw => (roots x,0))
    (of_program LPBinary.Program.maxFold) (pair roots_poly (const 0))

end MetricKMedian.Taper.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_TaperAllProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Taper.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly Finset
abbrev AllRaw := (Raw × List Bool) × ℕ

def colocated (x : ℚ × Row) : ℚ := (x.2.map (fun q => if q=0 then x.1 else 0)).sum
def extras (x : (Row × List Bool) × ℕ) : List ℕ :=
  ((RoundingList.indices x.1.1).filter (fun i => decide (x.1.1[i]?.getD 0=0) && !(x.1.2[i]?.getD false))).take (x.2-(x.1.2.filter id).length)
def zeroRow (x : (Row × List Bool) × ℕ) : Row :=
  (RoundingList.indices x.1.1).map (fun i => if x.1.2[i]?.getD false || natMember (extras x,i) then 1 else 0)
def sourceRow (x : AllRaw) : Row :=
  if 1 ≤ colocated (x.1.1.1.1,x.1.1.2) then zeroRow ((x.1.1.2,x.1.2),x.2)
  else x.1.1.2.map (fun d => rationalMarginal x.1.1.1.2 d (radius x.1.1))

@[fun_prop] theorem colocated_poly : Poly colocated := by
  unfold colocated
  apply comp rat_sum
  apply list_map <;> fun_prop
@[fun_prop] theorem extras_poly : Poly extras := by
  unfold extras
  have hf : Poly (fun x : (Row × List Bool) × ℕ =>
      (RoundingList.indices x.1.1).filter (fun i => decide (x.1.1[i]?.getD 0=0) && !(x.1.2[i]?.getD false))) := by
    apply list_filter <;> fun_prop
  have hc : Poly (fun x : (Row × List Bool) × ℕ => x.1.2.filter id) := by
    apply list_filter <;> fun_prop
  exact comp (f:=fun x : List ℕ × ℕ => x.1.take x.2)
    (g:=fun x : (Row × List Bool) × ℕ => (((RoundingList.indices x.1.1).filter (fun i => decide (x.1.1[i]?.getD 0=0) && !(x.1.2[i]?.getD false))),x.2-(x.1.2.filter id).length))
    list_take (pair hf (by fun_prop))
@[fun_prop] theorem zeroRow_poly : Poly zeroRow := by
  unfold zeroRow
  apply list_map <;> fun_prop
@[fun_prop] theorem sourceRow_poly : Poly sourceRow := by
  unfold sourceRow
  have hm : Poly (fun x : AllRaw => x.1.1.2.map (fun d => rationalMarginal x.1.1.1.2 d (radius x.1.1))) := by
    apply list_map
    · unfold rationalMarginal; fun_prop
    · fun_prop
  fun_prop

end MetricKMedian.Taper.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliListOperations
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.SparseBernoulli.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly

@[fun_prop] theorem units_poly (d : ℕ) : Poly (units d) := by
  induction d with
  | zero => exact const [()]
  | succ d ih =>
    change Poly (fun q => (false::q).flatMap (fun _ => units d q))
    apply list_flatMap
    · exact comp ih fst
    · fun_prop

@[simp] theorem units_length (d : ℕ) (q : Row) : (units d q).length=(q.length+1)^d := by
  induction d with
  | zero => simp [units]
  | succ d ih => simp [units,List.length_flatMap,ih,pow_succ,Nat.mul_comm]; ring

def tests (d : ℕ) (q : Row) (j : ℕ) : List Bool :=
  (List.range d).map (fun a => q[j/(q.length+1)^a%(q.length+1)]?.getD true)
def value (d : ℕ) (q : Row) (j : ℕ) : ℚ := if (tests d q j).all id then 1 else 0
def featureList (d : ℕ) (q : Row) : List ℚ :=
  (List.range (units d q).length).map (value d q)

@[fun_prop] theorem tests_poly (d : ℕ) : Poly (fun x : Row × ℕ => tests d x.1 x.2) := by
  apply fixed_map
  intro a ha
  have hp : Poly (fun q : Row => (q.length+1)^a) := comp (nat_pow a) (by fun_prop)
  fun_prop
@[fun_prop] theorem value_poly (d : ℕ) : Poly (fun x : Row × ℕ => value d x.1 x.2) := by
  unfold value
  fun_prop
@[fun_prop] theorem featureList_poly (d : ℕ) : Poly (featureList d) := by
  apply list_map
  · exact comp (value_poly d) (by fun_prop)
  · exact comp (f:=fun xs : List Unit => List.range xs.length) (g:=units d) list_indices (units_poly d)

 def endpoint (t : ℕ) (b : Bool) (q : Row) : Row :=
   (List.range q.length).map (fun i => if i=t then b else q[i]?.getD false)
@[fun_prop] theorem endpoint_poly (b : Bool) : Poly (fun x : ℕ × Row => endpoint x.1 b x.2) := by
  apply list_map
  · fun_prop
  · exact comp (f:=fun xs : Row => List.range xs.length) (g:=Prod.snd) list_indices snd

end MetricKMedian.SparseBernoulli.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseProductProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section

namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.Automatic Binary.Automatic.Poly
variable {α β A B : Type}

@[fun_prop] theorem prodData_poly [Coding A] [Coding B] [Inhabited A] [Inhabited B] :
    Poly (prodData (A:=A) (B:=B)) := by
  unfold prodData
  apply pair
  · apply pair
    · fun_prop
    · apply list_flatMap
      · apply list_map <;> fun_prop
      · fun_prop
  · apply list_flatMap
    · apply list_map <;> fun_prop
    · fun_prop
end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_TaperGraphProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.TaperGraphProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseIntegerLaw.BinarySparse
def rawQ (x : Raw) : List Unit × List Row :=
  (x.2.map (fun _ => ()),x.2.map (fun col => Taper.ListOperation.sourceRow (((x.1.1,col.1),col.2),x.1.2)))
end MetricKMedian.TaperGraphProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBindProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.Automatic Binary.Automatic.Poly Finset

variable {α β A : Type}

@[fun_prop] theorem weights_poly : Poly weights := by
  unfold weights
  apply list_map <;> fun_prop

@[fun_prop] theorem jointWeights_poly [Coding A] [Inhabited A] : Poly (jointWeights (A:=A)) := by
  unfold jointWeights
  apply list_flatMap
  · apply list_map <;> fun_prop
  · fun_prop

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_FractionalScanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.FractionalRefinement.ScanProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram
structure Input extends Program.Input where
  m : ℕ
  metric : PseudoMetricSpace (Fin m)
  facility : Fin f → Fin m
  client : Fin j → Fin m
  hdf : ∀ b b', @dist _ metric.toDist (facility b) (facility b')=(df b b':ℝ)
  hc : ∀ c b, @dist _ metric.toDist (client c) (facility b)=(dc c b:ℝ)
  hcc : ∀ c c', @dist _ metric.toDist (client c) (client c')=(dd c c':ℝ)
  B : ℚ
end MetricKMedian.Preparation.FractionalRefinement.ScanProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Classes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Complexity
open Binary.Automatic Binary.Automatic.Poly

def firstWord (s : Word) : Word :=
  let a := InputParser.natRead s
  a.2.take a.1

end MetricKMedian.Complexity

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Encoding
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Binary Binary.Automatic Binary.Automatic.Poly

namespace Raw

def parse (xs : List Bool) : Raw :=
  let a := InputParser.natRead xs
  let b := InputParser.natRead a.2
  let c := InputParser.natRead b.2
  (a.1, b.1, c.1, c.2)

@[fun_prop] theorem parse_poly : Poly parse := by unfold parse; fun_prop

def indices (r : Raw) : List ℕ :=
  List.range ((r.table.take r.m ++ r.table.take r.n).length)

@[fun_prop] theorem indices_poly : Poly indices := by
  unfold indices
  apply Poly.comp Poly.list_indices
  dsimp only [m, n, table]
  apply Poly.comp (f := fun lists : List Bool × List Bool => lists.1 ++ lists.2)
    (g := fun raw : Raw => (raw.2.2.2.take raw.1, raw.2.2.2.take raw.2.1))
    Poly.list_append
  apply Poly.pair
  · exact Poly.comp (f := fun input : List Bool × ℕ => input.1.take input.2)
      InputParser.take_poly (g := fun raw : Raw => (raw.2.2.2, raw.1)) (by fun_prop)
  · exact Poly.comp (f := fun input : List Bool × ℕ => input.1.take input.2)
      InputParser.take_poly (g := fun raw : Raw => (raw.2.2.2, raw.2.1)) (by fun_prop)

@[fun_prop] theorem bits_poly : Poly Nat.bits := ⟨bitsProgram⟩

end Raw

end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end


