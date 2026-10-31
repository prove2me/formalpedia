-- Prove2me | Definitions.Def_OAIQ053K015
-- name    : OAIQ053K015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:55:49.707618+00:00
-- url     : https://prove2.me/theorems/3d246fe6-8fe5-41d4-971a-a04e7e13d2e4
-- title:
--   Definitions bundle OAIQ053K015 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 125 declarations of OpenAI's Lean: 62 definitions, 5 inductive types or structures, 3 instances and 55 theorems. The definitions and types are `OAI.MetricKMedian.Binary.BooleanLists.pack`, `OAI.MetricKMedian.Binary.BooleanLists.unpack`, `OAI.MetricKMedian.Binary.PolyProgram.stock`, `OAI.MetricKMedian.Binary.Repeat.enc`, `OAI.MetricKMedian.Binary.WordTransducer.listBits`, `OAI.MetricKMedian.Completion.Rational.Program.Input`, `OAI.MetricKMedian.Completion.Rational.Program.Input.packing`, `OAI.MetricKMedian.Completion.Rational.instLinearOrderCopy`, `OAI.MetricKMedian.Completion.Rational.output`, `OAI.MetricKMedian.Completion.Rational.pick`, `OAI.MetricKMedian.Complexity.FiniteComposition.PolyProgram`, `OAI.MetricKMedian.Complexity.FiniteComposition.PolyProgram.comp`, `OAI.MetricKMedian.Complexity.FiniteComposition.PolyProgram.compTime`, `OAI.MetricKMedian.Complexity.FiniteComposition.PolyProgram.congr`, `OAI.MetricKMedian.Complexity.FiniteComposition.PolyProgram.sizeBound`, `OAI.MetricKMedian.Complexity.FiniteComposition.PolyProgram.stock`, `OAI.MetricKMedian.Complexity.FiniteComposition.PolyProgram.stockMachine`, `OAI.MetricKMedian.Complexity.FiniteComposition.PolyProgram.thread`, `OAI.MetricKMedian.Complexity.FiniteComposition.Thread.Alphabet`, `OAI.MetricKMedian.Complexity.FiniteComposition.Thread.Key`, `OAI.MetricKMedian.Complexity.FiniteComposition.Thread.Label`, `OAI.MetricKMedian.Complexity.FiniteComposition.Thread.State`, `OAI.MetricKMedian.Complexity.FiniteComposition.Thread.body`, `OAI.MetricKMedian.Complexity.FiniteComposition.Thread.buffer`, `OAI.MetricKMedian.Complexity.FiniteComposition.Thread.clean`, `OAI.MetricKMedian.Complexity.FiniteComposition.Thread.code`, `OAI.MetricKMedian.Complexity.FiniteComposition.Thread.drainCfg`, `OAI.MetricKMedian.Complexity.FiniteComposition.Thread.drainCode`, `OAI.MetricKMedian.Complexity.FiniteComposition.Thread.draining`, `OAI.MetricKMedian.Complexity.FiniteComposition.Thread.emitCfg`, `OAI.MetricKMedian.Complexity.FiniteComposition.Thread.emitCode`, `OAI.MetricKMedian.Complexity.FiniteComposition.Thread.emitting`, `OAI.MetricKMedian.Complexity.FiniteComposition.Thread.loadCfg`, `OAI.MetricKMedian.Complexity.FiniteComposition.Thread.loadCode`, `OAI.MetricKMedian.Complexity.FiniteComposition.Thread.loading`, `OAI.MetricKMedian.Complexity.FiniteComposition.Thread.machine`, `OAI.MetricKMedian.Complexity.FiniteComposition.Thread.readCfg`, `OAI.MetricKMedian.Complexity.FiniteComposition.Thread.readCode`, `OAI.MetricKMedian.Complexity.FiniteComposition.Thread.reading`, `OAI.MetricKMedian.Complexity.FiniteComposition.Thread.slot` and 27 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Binary_BinaryAutomatic`, `KMedian_Binary_BinaryBooleanLists`, `KMedian_Binary_BinaryDyadicPowers`, `KMedian_Binary_BinaryFloor`, `KMedian_Binary_BinaryListExtras`, `KMedian_Binary_BinaryRepeat`, `KMedian_Binary_BooleanMachine`, `KMedian_Binary_BooleanPolynomial`, `KMedian_Compression_CompressionListStep`, `KMedian_Compression_RationalOperationHeight`, `KMedian_Geometry_GraphListOperations`, `KMedian_Geometry_RationalGridRound`, `KMedian_Geometry_RationalParameterizedHistory`, `KMedian_Geometry_RationalUnitInput`, `KMedian_Hardness_Composition`, `KMedian_Hardness_Threads`, `KMedian_Optimization_ApproximationListProgram`, `KMedian_Optimization_ComputedNearest`, `KMedian_Optimization_FractionalInputProgram`, `KMedian_Optimization_LPListFacts`, `KMedian_Optimization_LPMinimumSelection`, `KMedian_Preparation_AssignmentCopies`, `KMedian_Process_CopyGraphProgram`, `KMedian_Process_CopyTransport`, `KMedian_Process_PhysicalPotential`, `KMedian_Process_RoundingListOperations`, `KMedian_Programs_GreedyPackingProgram`, `KMedian_Programs_HistorySelectionProgram`, `KMedian_Programs_NearestListProgram`, `KMedian_Reduction_CompletionProgram`, `KMedian_Reduction_RationalGreedyCompletion`, `KMedian_Rounding_RationalPhysicalKernel`, `KMedian_Rounding_RationalRoundParameters`, `KMedian_Sparse_SparseBindProgram`, `KMedian_Sparse_SparseIterationHeight`.
--
--   **Imports.** It imports the bundles `OAIQ053K000`, `OAIQ053K001`, `OAIQ053K002`, `OAIQ053K003` and `OAIQ053K004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K029`, `OAIQ053K030`, `OAIQ053K031`, `OAIQ053K032`, `OAIQ053K033`, `OAIQ053K034`, `OAIQ053K035`, `OAIQ053K036` and `OAIQ053K037`; the statement `OAI.MetricKMedian.FixedBatch.forced_step_local_bound_s53`; the proof of `OAI.MetricKMedian.FixedBatch.forced_step_local_bound_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K000
import Definitions.Def_OAIQ053K001
import Definitions.Def_OAIQ053K002
import Definitions.Def_OAIQ053K003
import Definitions.Def_OAIQ053K004

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BooleanMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Turing StateTransition Function Finset

attribute [instance] Machine.decK Machine.finK Machine.finLabel Machine.finState

namespace Machine

instance allWorkFinite (M : Machine) (k : M.tm.K) : Fintype (M.tm.Γ k) :=
  inferInstanceAs (Fintype Bool)

end Machine

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BooleanPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Turing Polynomial

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
variable {f : α → β} {g : β → γ}

def stock (P : PolyProgram ea eb f) : TM2ComputableInPolyTime ea eb f where
  tm := P.machine.tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := P.time
  outputsFun a := by
    have h := P.outputs a
    dsimp only [Machine.tm,Equiv.refl] at h ⊢
    simpa only [List.map_id] using h

 theorem finite_work (P : PolyProgram ea eb f) (k : P.stock.tm.K) : Finite (P.stock.tm.Γ k) :=
  inferInstanceAs (Finite Bool)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryListExtras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace WordTransducer

def listBits : Transducer where
  Q := Unit
  initial := ()
  next _ b := ((),[true,b,false])
  finish _ := []
end WordTransducer
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_RationalOperationHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.Binary
open Finset

namespace HasHeight
variable {q r : ℚ} {L M : ℕ}

 theorem zero (L : ℕ) : HasHeight 0 L := by
  constructor
  · simp
  · simp only [Rat.den_zero,Int.natCast_one]
    exact one_le_pow₀ (by norm_num)

 theorem one (L : ℕ) : HasHeight 1 L := by
  constructor <;> simp only [Rat.num_one,Rat.den_one,abs_one,Int.natCast_one] <;>
    exact one_le_pow₀ (by norm_num)

 theorem neg (h : HasHeight q L) : HasHeight (-q) L := by
  simpa only [HasHeight,Rat.num_neg_eq_neg_num,Rat.den_neg_eq_den,abs_neg] using h

 theorem inv (hq : HasHeight q L) : HasHeight q⁻¹ L := by
  by_cases hq0 : q=0
  · rw [hq0,inv_zero]
    exact zero L
  have hqn : q.num ≠ 0 := by
    intro h
    apply hq0
    rw [← Rat.num_div_den q,h,Int.cast_zero,zero_div]
  have hh := Gaussian.ratio_num_den_bound (q.den:ℤ) q.num hqn ((2:ℤ)^L)
    (by simpa only [abs_of_nonneg (Int.natCast_nonneg _)] using hq.2) hq.1
  have he : ((q.den:ℤ):ℚ)/(q.num:ℚ)=q⁻¹ := by
    conv_rhs => rw [← Rat.num_div_den q]
    simp only [inv_div,Int.cast_natCast]
  rwa [he] at hh

 theorem div (hq : HasHeight q L) (hr : HasHeight r M) : HasHeight (q/r) (L+M) := by
  simpa only [div_eq_mul_inv] using hq.mul hr.inv

 theorem sub (hq : HasHeight q L) (hr : HasHeight r M) : HasHeight (q-r) (L+M+1) := by
  simpa only [sub_eq_add_neg] using hq.add hr.neg

end HasHeight
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_LPListFacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section
namespace MetricKMedian.LPBinary
open Finset
abbrev Rows := List Row
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryAutomatic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Binary.Automatic
open PolyProgram Function
instance instCodingUnit : Coding Unit := ⟨fun _ => []⟩
end MetricKMedian.Binary.Automatic
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryBooleanLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Binary
namespace BooleanLists
def pack : Transducer where
  Q := Unit
  initial := ()
  next := fun _ b => ((),[true,b,false])
  finish := fun _ => []
def unpack : Transducer where
  Q := Phase
  initial := .start
  next := fun q b => match q with
    | .start => (.value,[])
    | .value => (.stop,[b])
    | .stop => (.start,[])
  finish := fun _ => []
end BooleanLists
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryDyadicPowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Binary
open Function Polynomial PolyProgram
namespace Dyadic

theorem height_pow (i : ℕ) : HasHeight ((2:ℚ)^i) i := by
  induction i with
  | zero => simpa using HasHeight.one 0
  | succ i ih =>
      rw [pow_succ]
      exact ih.mul (by norm_num [HasHeight])
end Dyadic
end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryFloor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section
namespace MetricKMedian.Binary.Automatic.Poly
 theorem natFloor_eq (q : ℚ) : ⌊q⌋₊=if q<0 then 0 else q.num.natAbs/q.den := by
  by_cases h : q<0
  · simp only [ite_eq_left h,Nat.floor_of_nonpos h.le]
  · rw [ite_eq_right h]
    have hn : 0≤q.num := Rat.num_nonneg.mpr (le_of_not_gt h)
    have he : ((q.num.natAbs:ℕ):ℚ)/(q.den:ℚ)=q := by
      rw [← Int.cast_natCast,Int.natCast_natAbs,abs_of_nonneg hn,Rat.num_div_den]
    calc
      ⌊q⌋₊=⌊((q.num.natAbs:ℕ):ℚ)/(q.den:ℚ)⌋₊ := congrArg Nat.floor he.symm
      _ = _ := Rat.natFloor_natCast_div_natCast _ _
end MetricKMedian.Binary.Automatic.Poly
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BinaryRepeat
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                    
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace Repeat
variable {α : Type}
abbrev enc (ea : α → List Bool) := encodePair Nat.bits ea

theorem run (ea : α → List Bool) (f : α → α) (N A n : ℕ) (a : α)
    (hn : n≤N) (ha : ∀ i≤n, (ea (f^[i] a)).length≤A) :
    BoundedRun (enc ea) (body f) (2*(N+1)+1+A) (n+1) (n,a) (f^[n] a) := by
  induction n generalizing a with
  | zero =>
      have has : (ea a).length≤A := by simpa using ha 0 (Nat.zero_le _)
      have hsize : (enc ea (0,a)).length ≤ 2*(N+1)+1+A := by
        simp only [enc,encodePair_length,Nat.zero_bits,List.length_nil]; omega
      exact BoundedRun.stop hsize (by simp [body])
  | succ n ih =>
      have hnl : (n+1).bits.length≤N+1 := (NatBinary.length_le_height (Nat.lt_two_pow_self.le)).trans (by omega)
      have has : (ea a).length≤A := by simpa using ha 0 (Nat.zero_le _)
      have hsize : (enc ea (n+1,a)).length ≤ 2*(N+1)+1+A := by
        simp only [enc,encodePair_length]; omega
      have hh := ih (f a) (by omega) (fun i hi => by
        simpa only [Function.iterate_succ_apply] using ha (i+1) (by omega))
      simpa only [Function.iterate_succ_apply] using
        (BoundedRun.step hsize (by simp [body]) hh)
end Repeat

end MetricKMedian.Binary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_ComputedNearest
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {n : ℕ}

theorem firstNearest_spec (U : Finset (Fin n)) (d : Fin n → ℚ) (hU : U.Nonempty) :
    firstNearest U d hU ∈ U ∧ ∀ i ∈ U, d (firstNearest U d hU) ≤ d i := by
  let B := U.filter (fun i => d i=(U.image d).min' (hU.image _))
  have hB : B.Nonempty := by
    obtain ⟨a,ha,he⟩ := mem_image.mp (min'_mem (U.image d) (hU.image _))
    exact ⟨a,mem_filter.mpr ⟨ha,he⟩⟩
  change B.min' hB ∈ U ∧ ∀ i ∈ U, d (B.min' hB) ≤ d i
  have hh := mem_filter.mp (min'_mem B hB)
  refine ⟨hh.1,?_⟩
  intro i hi
  rw [hh.2]
  exact min'_le _ _ (mem_image.mpr ⟨i,hi,rfl⟩)

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_LPMinimumSelection
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Finset

 theorem firstNearest_value {n : ℕ} (U : Finset (Fin n)) (d : Fin n → ℚ) (hU : U.Nonempty) :
    d (Preparation.firstNearest U d hU)=(U.image d).min' (hU.image _) := by
  unfold Preparation.firstNearest
  exact (mem_filter.mp (min'_mem (U.filter (fun i => d i=(U.image d).min' (hU.image _))) _)).2

 theorem firstNearest_le {n : ℕ} (U : Finset (Fin n)) (d : Fin n → ℚ) (hU : U.Nonempty)
    (j : Fin n) (hj : j∈U) (hd : d j=d (Preparation.firstNearest U d hU)) :
    Preparation.firstNearest U d hU ≤ j := by
  unfold Preparation.firstNearest
  apply min'_le
  exact mem_filter.mpr ⟨hj,hd.trans (firstNearest_value U d hU)⟩

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_CompressionListStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function Finset
abbrev Rows := Binary.IntegerList.Rows
abbrev LawData := ListPivot.LawData

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingListOperations
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.RoundingList
open Binary Binary.Automatic Binary.Automatic.Poly Finset
def probability (β p : Row) : ℚ :=
  if active p then
    down p (first p) (second p) (ratio β p) /
      (up p (first p) (second p) (ratio β p)+down p (first p) (second p) (ratio β p))
  else 0

def endpoint (β p : Row) (b : Bool) : Row :=
  if active p then move p (first p) (second p) (ratio β p)
    (if b then -down p (first p) (second p) (ratio β p) else up p (first p) (second p) (ratio β p))
  else p

end MetricKMedian.RoundingList
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_GraphListOperations
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseGraph.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly
def setView {n : ℕ} (S : Finset (Fin n)) : Row := List.ofFn (fun h => decide (h∈S))
end MetricKMedian.SparseGraph.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential

open Analytic

variable {I : Type*}

noncomputable def savingsFraction (g : ℝ) : ℝ :=
  min 1 (2 * P 1 * g / (1 + 1 / g))

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CopyTransport
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
attribute [-simp] _root_.OAI.MetricKMedian.CopyState.mem_own
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential
variable {F : Type*} [DecidableEq F] {Δ : ℕ}

noncomputable def localSet (A S : Finset (Copy (F := F) Δ)) : Finset A :=
  univ.filter (fun i => i.val ∈ S)

@[simp] theorem mem_localSet (A S : Finset (Copy (F := F) Δ)) (i : A) :
    i ∈ localSet A S ↔ i.val ∈ S := by simp [localSet]

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalPhysicalKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset
variable {F : Type} [LinearOrder F] [Fintype F] {Δ : ℕ}

local instance instLinearOrderCopy : LinearOrder (CopyState.Copy (F := F) Δ) := copyOrder

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_RationalGreedyCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.Completion.Rational
open Finset PhysicalPotential CopyState Preparation
variable {j : ℕ} {I : Type*} [DecidableEq I]

variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}
local instance instLinearOrderCopy : LinearOrder (Copy (F := F) Δ) := RationalPhysicalKernel.copyOrder

def pick (B : Fin j → Finset (Copy (F := F) Δ))
    (hB : ∀ c, (B c).Nonempty) (c : Fin j) : Copy (F := F) Δ := (B c).min' (hB c)

def output (d : Fin j → F → ℚ) (R : Fin j → ℚ)
    (A : Finset (Copy (F := F) Δ)) (B : Fin j → Finset (Copy (F := F) Δ))
    (hB : ∀ c, (B c).Nonempty) : Finset F :=
  integral Δ A ∪ (packing j (uncovered d R A) R B).image (fun c => (pick B hB c).1)

end MetricKMedian.Completion.Rational
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalRoundParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.FixedBatch
open PhysicalPotential

structure RationalParameters (τ : ℝ) where
  Δ : ℕ
  g : ℚ
  h : ℚ
  φ : ℚ
  β : ℚ
  ζ : ℚ
  T : ℕ
  taper : Fin T → ℚ
  Δpos : 0<Δ
  gpos : 0<(g:ℝ)
  gle : (g:ℝ)≤1
  unit : (g:ℝ)*(Δ:ℝ)=1
  hpos : 0<(h:ℝ)
  hle : (h:ℝ)≤1
  φpos : 0<(φ:ℝ)
  φle : (φ:ℝ)≤1
  βpos : 0<(β:ℝ)
  ζpos : 0<(ζ:ℝ)
  ζle : (ζ:ℝ)<1/4
  probability : (1+(φ:ℝ))*(2*(h:ℝ)*(g:ℝ))≤1
  small : (16*((Δ^2+Δ:ℕ):ℝ)+10)*(h:ℝ)≤ savingsFraction (g:ℝ)
  survival : (2*(h:ℝ)*(g:ℝ))*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ))≤1
  count : 8*(2*(h:ℝ)*(g:ℝ))*(Δ:ℝ)≤(φ:ℝ)*(g:ℝ)
  error : (T:ℝ)*(h:ℝ)*((g:ℝ)+12*(ζ:ℝ))+
    (T:ℝ)*batchConstant Δ*(h:ℝ)*((φ:ℝ)+(h:ℝ))*(Δ:ℝ)+
    5*(Δ:ℝ)*Real.exp (-(T:ℝ)*(h:ℝ)/2)≤τ
  failure : (T:ℝ)*(96*(Δ:ℝ)^2*(β:ℝ)/((2*(h:ℝ)*(g:ℝ))*(φ:ℝ)^2*(g:ℝ)))≤τ
  taper_pos : ∀ t, 0<(taper t:ℝ)
  taper_le : ∀ t, (taper t:ℝ)≤1/2
  taper_error : ∀ t, |(taper t:ℝ)-Analytic.P (Real.exp (-(t.val:ℝ)*(h:ℝ)))|≤(ζ:ℝ)

end MetricKMedian.FixedBatch
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalParameterizedHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                    
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
variable {τ : ℝ} (q : RationalParameters τ)

def probabilityQ : ℚ := 2*q.h*q.g

def allowance : ℚ := (q.T:ℚ)*(4/(q.g*q.β))

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_AssignmentCopies
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential
variable {F : Type} [Fintype F] [DecidableEq F] {Δ : ℕ}

def embedSlots (n : F → ℕ) (hn : ∀ a, n a ≤ Δ) : (Σ a, Fin (n a)) → Copy (F := F) Δ :=
  fun a => (a.1,⟨a.2.val,lt_of_lt_of_le a.2.isLt (hn a.1)⟩)

def activeSlots (n : F → ℕ) (hn : ∀ a, n a ≤ Δ) : Finset (Copy (F := F) Δ) :=
  univ.image (embedSlots n hn)

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalGridRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
open Preparation.RationalNearest
variable {τ : ℝ} (q : RationalParameters τ)
variable {F X : Type} [LinearOrder F] [PseudoMetricSpace X] {j : ℕ}
local instance rationalGridRoundCopyOrder : LinearOrder (Copy (F := F) q.Δ) := copyOrder

def nearest (d : Fin j → F → ℚ) (A : Finset (Copy (F := F) q.Δ)) :
    Fin j → Finset (Copy (F := F) q.Δ) := fun c => takeNearest (fun a => d c a.1) q.Δ A

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalUnitInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Preparation
open Finset

namespace RationalUnitInput
variable {f j : ℕ} (U : RationalUnitInput f j)

structure Realization (X : Type) [PseudoMetricSpace X] where
  i : Fin f → X
  c : Fin j → X
  hdf : ∀ a b, dist (i a) (i b)=(U.df a b:ℝ)
  hdc : ∀ c' a, dist (c c') (i a)=(U.dc c' a:ℝ)
  hdd : ∀ c' c'', dist (c c') (c c'')=(U.dd c' c'':ℝ)

end RationalUnitInput
end MetricKMedian.Preparation
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

def entries (ys ds : Row) : List Entry :=
  let es := ys.zip ds
  (List.range es.length).zip es

def filling (ys ds : Row) : Row := let es := entries ys ds; es.map (amount es)

end Nearest
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_GreedyPackingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Completion.Rational.PackingProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Polynomial
open SparseGraph.ListOperation (Row setView indices)
open MaskProgram

 theorem advance_result (x : Input) (t : ℕ) (s : Cut x) :
    ((advance x)^[t] s).2=s.2 ∪ packing t s.1 x.R x.B := by
  induction t generalizing s with
  | zero => simp only [Function.iterate_zero,Function.id_def,packing,union_empty]
  | succ t ih =>
    rw [Function.iterate_succ_apply,ih]
    by_cases h : s.1.Nonempty
    · simp only [advance,dite_eq_left h,packing]
      ext i
      simp only [mem_union,mem_insert]
      tauto
    · have he : s.1=∅ := not_nonempty_iff_eq_empty.mp h
      simp [advance,he,packing_empty]

end MetricKMedian.Completion.Rational.PackingProgram
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
open SparseGraph.ListOperation (Row setView indices)
open MetricKMedian.MaskProgram

def assignmentData (z : Raw) : Matrix := z.2.1.map (fun d => LPBinary.Nearest.filling z.1 d)
end MetricKMedian.Preparation.FractionalRefinement.Program
end

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
abbrev Output := Row × Rows
end Repair
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseIterationHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Binary.HasHeight
variable {q r : ℚ} {L : ℕ}
theorem min (hq : HasHeight q L) (hr : HasHeight r L) : HasHeight (min q r) L := by
  rcases le_total q r with h | h
  · rwa [min_eq_left h]
  · rwa [min_eq_right h]
end MetricKMedian.Binary.HasHeight

end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CopyGraphProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.RationalPhysicalKernel.CopyGraphProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row setView)
open CopyList

 theorem rank_owner {f Δ : ℕ} (a : CopyState.Copy (F:=Fin f) Δ) :
    (rank a).val/Δ=a.1.val := by
  change (a.2.val+Δ*a.1.val)/Δ=a.1.val
  have hd : 0<Δ := Nat.zero_lt_of_lt a.2.isLt
  rw [Nat.add_comm,Nat.mul_add_div hd,Nat.div_eq_of_lt a.2.isLt,Nat.add_zero]

end MetricKMedian.RationalPhysicalKernel.CopyGraphProgram
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

def weights (x : LawData) : List ℚ := x.2.map (fun z : ℤ => (z:ℚ)/(x.1:ℚ))
def jointWeights (x : LawData × List (Data A)) : List ℚ :=
  ((weights x.1).zip x.2).flatMap (fun z => (weights z.2.1).map (fun q => z.1*q))
def bindData (x : LawData × List (Data A)) : Data A :=
  ((IntegerList.denominator (jointWeights x),IntegerList.numerators (jointWeights x)),
    x.2.flatMap Prod.snd)

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_CompletionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Completion.Rational.Program
open Finset CopyState Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row setView indices)
open MaskProgram MaskOperations RationalPhysicalKernel.CopyList

local instance instLinearOrderCopyFin_r31458b_1 {f Δ : ℕ} : LinearOrder (Copy (F:=Fin f) Δ) := RationalPhysicalKernel.copyOrder
structure Input (Δ : ℕ) where
  f : ℕ
  j : ℕ
  d : Fin j → Fin f → ℚ
  R : Fin j → ℚ
  A : Finset (Copy (F:=Fin f) Δ)
  B : Fin j → Finset (Copy (F:=Fin f) Δ)
  hB : ∀ c, (B c).Nonempty
def Input.packing {Δ : ℕ} (x : Input Δ) : PackingProgram.Input :=
  ⟨x.j,x.f*Δ,x.R,(fun c => (x.B c).map finProdFinEquiv.toEmbedding),uncovered x.d x.R x.A⟩
end MetricKMedian.Completion.Rational.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_HistorySelectionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.FixedBatch.RationalParameters.SelectionProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row setView)
open RationalPhysicalKernel
variable {τ : ℝ} (q : RationalParameters τ)

local instance instLinearOrderCopyFin_r31458b_2 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
structure Input extends Completion.Rational.Program.Input q.Δ where
  d₀ : Fin f → Fin f → ℚ
end MetricKMedian.FixedBatch.RationalParameters.SelectionProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Composition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Complexity.FiniteComposition
open Turing Function Finset Polynomial
open Binary (Trace)

attribute [instance] Machine.decK Machine.finK Machine.finΓ Machine.finLabel Machine.finState

namespace Embedding
variable {K K' L S L' S' : Type} [DecidableEq K] [DecidableEq K']
  {Γ : K → Type} {Γ' : K' → Type}
variable (E : Embedding Γ L S Γ' L' S')

theorem trace (m : L → TM2.Stmt Γ L S) (m' : L' → TM2.Stmt Γ' L' S')
    (hm : ∀ l, m' (E.label l) = E.stmt (m l))
    {n : ℕ} {a b : TM2.Cfg Γ L S} (h : Trace (TM2.step m) n a b) :
    Trace (TM2.step m') n (E.cfg a) (E.cfg b) :=
  h.map E.cfg (E.step_cfg m m' hm)
end Embedding

namespace Compose
variable (M N : Machine)

theorem transfer_run (b : Bool) (xs ys : List Bool) :
    Trace (machine M N).step xs.length (transferCfg M N b xs ys)
      (transferCfg M N b [] (xs.reverse ++ ys)) := by
  induction xs generalizing ys with
  | nil => exact Trace.refl _
  | cons x xs ih =>
      have h := Trace.cons (transfer_cons M N b x xs ys) (ih (x :: ys))
      simpa only [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
        using h

theorem transfer_all (ys : List Bool) :
    Trace (machine M N).step (2 * ys.length + 2)
      ((left M N).cfg (M.finalCfg ys)) ((right M N).cfg (N.initialCfg ys)) := by
  have h₀ := transfer_run M N false ys []
  have h₁ := Trace.cons (transfer_empty M N false ys.reverse) (Trace.refl _)
  have h₂ := transfer_run M N true ys.reverse []
  have h₃ := Trace.cons (transfer_empty M N true ys) (Trace.refl _)
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h₀ h₂
  rw [boundary_false] at h₁
  rw [boundary_true] at h₃
  have hh := ((h₀.trans h₁).trans h₂).trans h₃
  rw [left_final]
  convert hh using 1; omega

theorem run {t u : ℕ} {xs ys zs : List Bool}
    (hM : Trace M.step t (M.initialCfg xs) (M.finalCfg ys))
    (hN : Trace N.step u (N.initialCfg ys) (N.finalCfg zs)) :
    Trace (machine M N).step (t + 2 * ys.length + 2 + u)
      ((machine M N).initialCfg xs) ((machine M N).finalCfg zs) := by
  have hL := (left M N).trace M.code (machine M N).code (code_left M N) hM
  have hR := (right M N).trace N.code (machine M N).code (code_right M N) hN
  have h := (hL.trans (transfer_all M N ys)).trans hR
  rw [initial_left, final_right] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl

end Compose

namespace Machine
variable {K L S : Type} {Γ : K → Type} [DecidableEq K]

variable [Fintype K]

theorem volume_update (s : ∀ k, List (Γ k)) (k : K) (v : List (Γ k)) :
    volume (update s k v)+(s k).length=volume s+v.length := by
  classical
  unfold volume
  have he : (fun j => (update s k v j).length)=update (fun j => (s j).length) k v.length := by
    funext j
    by_cases h : j = k
    · subst j; simp
    · simp [Function.update_of_ne h]
  rw [he,Finset.sum_update_of_mem (mem_univ k)]
  have hh := Finset.sum_erase_add (univ : Finset K) (fun j => (s j).length) (mem_univ k)
  simp only [Finset.sdiff_singleton_eq_erase]
  omega

theorem stepAux_volume (q : TM2.Stmt Γ L S)
    (v : S) (s : ∀ k, List (Γ k)) :
    volume (TM2.stepAux q v s).stk ≤ volume s+pushes q := by
  induction q generalizing v s with
  | push k g q ih =>
      have h := ih v (update s k (g v::s k))
      have hv := volume_update s k (g v::s k)
      simp only [List.length_cons] at hv
      simpa only [TM2.stepAux,pushes,Nat.add_assoc] using (by omega :
        volume (TM2.stepAux q v (update s k (g v::s k))).stk≤volume s+(1+pushes q))
  | peek k g q ih => exact ih _ _
  | pop k g q ih =>
      have h := ih (g v (s k).head?) (update s k (s k).tail)
      have hv := volume_update s k (s k).tail
      have hl := List.length_tail (l := s k)
      simp only [TM2.stepAux,pushes]
      omega
  | load g q ih => exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v
      · simpa only [TM2.stepAux,hg,Bool.false_eq_true,Bool.cond_false,pushes] using
          (ihr v s).trans (Nat.add_le_add_left (le_max_right (pushes q) _) _)
      · simpa only [TM2.stepAux,hg,Bool.cond_true,pushes] using
          (ihq v s).trans (Nat.add_le_add_left (le_max_left _ (pushes r)) _)
  | goto g => simp only [TM2.stepAux,pushes,Nat.add_zero,le_refl]
  | halt => simp only [TM2.stepAux,pushes,Nat.add_zero,le_refl]

theorem step_volume (M : Machine) (a b : M.Cfg) (h : M.step a=some b) :
    volume b.stk ≤ volume a.stk+M.growth := by
  rcases a with ⟨l,v,s⟩
  cases l with
  | none => cases h
  | some l =>
      have hb : b=TM2.stepAux (M.code l) v s := (Option.some.inj h).symm
      rw [hb]
      exact (stepAux_volume _ _ _).trans (Nat.add_le_add_left
        (show pushes (M.code l) ≤ M.growth from
          single_le_sum (f:=fun x => pushes (M.code x)) (fun _ _ => Nat.zero_le _) (mem_univ l)) _)

theorem trace_volume (M : Machine) {n : ℕ} {a b : M.Cfg}
    (h : Trace M.step n a b) : volume b.stk ≤ volume a.stk+n*M.growth := by
  induction h with
  | refl => simp
  | @cons n a b c hab hbc ih =>
      have hs := M.step_volume a b hab
      calc
        _ ≤ volume b.stk+n*M.growth := ih
        _ ≤ volume a.stk+(n+1)*M.growth := by rw [Nat.add_mul]; omega

theorem volume_single (k : K) (xs : List (Γ k)) :
    volume (single k xs) = xs.length := by
  have h := volume_update (fun k : K => ([] : List (Γ k))) k xs
  simpa [volume, single] using h

@[simp] theorem initial_volume (M : Machine) (s : List Bool) :
    volume (M.initialCfg s).stk = s.length := by
  simp only [initialCfg, volume_single, List.length_map]

@[simp] theorem final_volume (M : Machine) (s : List Bool) :
    volume (M.finalCfg s).stk = s.length := by
  simp only [finalCfg, volume_single, List.length_map]

 theorem output_length (M : Machine) {s t : List Bool} {n : ℕ}
    (h : Trace M.step n (M.initialCfg s) (M.finalCfg t)) :
    t.length ≤ s.length+n*M.growth := by
  simpa only [initial_volume, final_volume] using M.trace_volume h

end Machine

structure PolyProgram {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (f : α → β) where
  machine : Machine
  time : Polynomial ℕ
  outputs : ∀ a, ∃ n, n ≤ time.eval (ea a).length ∧
    Trace machine.step n (machine.initialCfg (ea a)) (machine.finalCfg (eb (f a)))

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
variable {f : α → β} {g : β → γ}

noncomputable def stock (P : PolyProgram ea eb f) : TM2ComputableInPolyTime ea eb f where
  tm := P.machine.tm
  inputAlphabet := P.machine.inputAlphabet
  outputAlphabet := P.machine.outputAlphabet
  time := P.time
  outputsFun a := by
    let n := Classical.choose (P.outputs a)
    have hn := (Classical.choose_spec (P.outputs a)).1
    have ht := (Classical.choose_spec (P.outputs a)).2
    refine ⟨⟨n, ?_⟩, hn⟩
    change (flip Bind.bind P.machine.step)^[n]
      (some (initList P.machine.tm ((ea a).map P.machine.inputAlphabet.symm))) =
      some (haltList P.machine.tm ((eb (f a)).map P.machine.outputAlphabet.symm))
    rw [Machine.init_eq, Machine.halt_eq]
    exact ht.iterate_eq

noncomputable def stockMachine (p : TM2ComputableInPolyTime ea eb f)
    (h : ∀ k : p.tm.K, Finite (p.tm.Γ k)) : Machine := {
    K := p.tm.K
    finK := p.tm.kFin
    decK := p.tm.kDecidableEq
    Γ := p.tm.Γ
    finΓ := fun k => @Fintype.ofFinite (p.tm.Γ k) (h k)
    input := p.tm.k₀
    output := p.tm.k₁
    inputAlphabet := p.inputAlphabet
    outputAlphabet := p.outputAlphabet
    Label := p.tm.Λ
    finLabel := p.tm.ΛFin
    main := p.tm.main
    State := p.tm.σ
    finState := p.tm.σFin
    initial := p.tm.initialState
    code := p.tm.m }

noncomputable def sizeBound (P : PolyProgram ea eb f) : Polynomial ℕ :=
  X + P.time * C P.machine.growth

 theorem length_bound (P : PolyProgram ea eb f) (a : α) :
    (eb (f a)).length ≤ P.sizeBound.eval (ea a).length := by
  obtain ⟨n, hn, ht⟩ := P.outputs a
  have hl := P.machine.output_length ht
  simp only [sizeBound, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C]
  exact hl.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hn) _)

noncomputable def compTime (P : PolyProgram ea eb f) (Q : PolyProgram eb ec g) : Polynomial ℕ :=
  P.time + 2 * P.sizeBound + 2 + Q.time.comp P.sizeBound

noncomputable def comp (P : PolyProgram ea eb f) (Q : PolyProgram eb ec g) :
    PolyProgram ea ec (g ∘ f) where
  machine := Compose.machine P.machine Q.machine
  time := P.compTime Q
  outputs a := by
    obtain ⟨n, hn, ht⟩ := P.outputs a
    obtain ⟨m, hm, hu⟩ := Q.outputs (f a)
    refine ⟨n + (2 * (eb (f a)).length + 2) + m, ?_, Compose.run _ _ ht hu⟩
    have hl := P.length_bound a
    have hq := hm.trans (Binary.polynomial_eval_mono Q.time hl)
    simp only [compTime, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_comp]
    omega

 def congr (P : PolyProgram ea eb f) (f' : α → β) (h : ∀ a, f a = f' a) :
    PolyProgram ea eb f' where
  machine := P.machine
  time := P.time
  outputs a := by rw [← h a]; exact P.outputs a

end PolyProgram

end MetricKMedian.Complexity.FiniteComposition

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Threads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Complexity.FiniteComposition
open Turing Function Polynomial
open Binary (Trace quote quote_length polynomial_eval_mono)

namespace Thread
variable (M : Machine)
abbrev Key := M.K ⊕ Bool
abbrev Label := M.Label ⊕ Fin 4
abbrev State := M.State × Option Bool

abbrev Alphabet : Key M → Type
  | .inl k => M.Γ k
  | .inr _ => Bool

instance alphabetFinite (k : Key M) : Fintype (Alphabet M k) := by
  cases k with
  | inl k => exact M.finΓ k
  | inr k => exact inferInstanceAs (Fintype Bool)
abbrev source : Key M := .inr false
abbrev buffer : Key M := .inr true
abbrev reading : Label M := .inr 0
abbrev loading : Label M := .inr 1
abbrev emitting : Label M := .inr 2
abbrev draining : Label M := .inr 3

def store (s : ∀ k, List (M.Γ k)) (xs ys : List Bool) : ∀ k, List (Alphabet M k) :=
  fun k => match k with
  | .inl k => s k
  | .inr false => xs
  | .inr true => ys

@[simp] theorem store_local (s : ∀ k, List (M.Γ k)) (xs ys : List Bool) (k : M.K) :
    store M s xs ys (.inl k)=s k := rfl
@[simp] theorem store_source (s : ∀ k, List (M.Γ k)) (xs ys : List Bool) :
    store M s xs ys (source M)=xs := rfl
@[simp] theorem store_buffer (s : ∀ k, List (M.Γ k)) (xs ys : List Bool) :
    store M s xs ys (buffer M)=ys := rfl

def slot (k : M.K) (xs : List (M.Γ k)) : ∀ j, List (M.Γ j) := Machine.single k xs

 theorem slot_nil (k : M.K) : slot M k []=fun _ => [] := by
  funext j
  by_cases h : j = k
  · subst j; simp [slot, Machine.single]
  · simp [slot, Machine.single, Function.update_of_ne h]
 theorem slot_self (k : M.K) (xs : List (M.Γ k)) : slot M k xs k=xs := by simp [slot, Machine.single]
 theorem slot_update (k : M.K) (xs ys : List (M.Γ k)) : update (slot M k xs) k ys=slot M k ys := by
  funext j
  by_cases h : j = k
  · subst j; simp [slot, Machine.single]
  · simp [slot, Machine.single, Function.update_of_ne h]

 theorem store_update_local (s : ∀ k, List (M.Γ k)) (xs ys : List Bool) (k : M.K) (w : List (M.Γ k)) :
    update (store M s xs ys) (.inl k) w=store M (update s k w) xs ys := by
  funext j
  rcases j with j | j
  · by_cases h : j = k
    · subst j; simp [store]
    · simp [store, Function.update_of_ne h, Function.update_of_ne (mt Sum.inl.inj h)]
  · cases j <;> simp [store]
 theorem store_update_source (s : ∀ k, List (M.Γ k)) (xs ys w : List Bool) :
    update (store M s xs ys) (source M) w=store M s w ys := by
  funext j
  rcases j with j | j <;> try cases j
  all_goals simp [store]
 theorem store_update_buffer (s : ∀ k, List (M.Γ k)) (xs ys w : List Bool) :
    update (store M s xs ys) (buffer M) w=store M s xs w := by
  funext j
  rcases j with j | j <;> try cases j
  all_goals simp [store]

def body (tail : List Bool) : Embedding M.Γ M.Label M.State (Alphabet M) (Label M) (State M) where
  key := Sum.inl
  symbol k := Equiv.refl (M.Γ k)
  read := Prod.fst
  write v x := (x,v.2)
  state v := (v,none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s := store M s tail []
  stack_key s k := by exact (List.map_id (s k)).symm
  stack_update s k x := by
    change store M (update s k x) tail [] = update (store M s tail []) (Sum.inl k) (x.map id)
    rw [List.map_id]
    exact (store_update_local M s tail [] k x).symm
  label := Sum.inl
  halted := some (emitting M)
  stop := .goto (fun _ => emitting M)
  stop_spec _ _ := rfl

 theorem body_stmt (tail : List Bool) (s : TM2.Stmt M.Γ M.Label M.State) :
    (body M tail).stmt s=(body M []).stmt s := by
  induction s <;> simp_all [Embedding.stmt,body] <;> rfl

def clean (v : State M) : State M := (v.1,none)

def readCode : TM2.Stmt (Alphabet M) (Label M) (State M) :=
  .pop (source M) (fun v b => (v.1,b))
    (.branch (fun v => v.2.getD false)
      (.pop (source M) (fun v b => (v.1,b))
        (.push (buffer M) (fun v => v.2.getD false)
          (.load (clean M) (.goto (fun _ => reading M)))))
      (.load (clean M) (.goto (fun _ => loading M))))

def loadCode : TM2.Stmt (Alphabet M) (Label M) (State M) :=
  .pop (buffer M) (fun v b => (v.1,b))
    (.branch (fun v => v.2.isSome)
      (.push (.inl M.input) (fun v => M.inputAlphabet.symm (v.2.getD false))
        (.load (clean M) (.goto (fun _ => loading M))))
      (.load (clean M) (.goto (fun _ => .inl M.main))))

def emitCode : TM2.Stmt (Alphabet M) (Label M) (State M) :=
  .pop (.inl M.output) (fun v b => (v.1,b.map M.outputAlphabet))
    (.branch (fun v => v.2.isSome)
      (.push (buffer M) (fun _ => true) (.push (buffer M) (fun v => v.2.getD false)
        (.load (clean M) (.goto (fun _ => emitting M)))))
      (.push (buffer M) (fun _ => false)
        (.load (clean M) (.goto (fun _ => draining M)))))

def drainCode : TM2.Stmt (Alphabet M) (Label M) (State M) :=
  .pop (buffer M) (fun v b => (v.1,b))
    (.branch (fun v => v.2.isSome)
      (.push (source M) (fun v => v.2.getD false)
        (.load (clean M) (.goto (fun _ => draining M))))
      (.load (clean M) .halt))

def code : Label M → TM2.Stmt (Alphabet M) (Label M) (State M)
  | .inl l => (body M []).stmt (M.code l)
  | .inr i => if i=0 then readCode M else if i=1 then loadCode M else if i=2 then emitCode M else drainCode M

abbrev machine : Machine where
  K := Key M
  Γ := Alphabet M
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  input := source M
  output := source M
  Label := Label M
  main := reading M
  State := State M
  initial := (M.initial,none)
  code := code M

 theorem code_body (tail : List Bool) (l : M.Label) :
    (machine M).code ((body M tail).label l)=(body M tail).stmt (M.code l) := (body_stmt M tail _).symm

def readCfg (xs tail buf : List Bool) : (machine M).Cfg :=
  ⟨some (reading M),(M.initial,none),store M (fun _ => []) (quote xs++tail) buf⟩

def loadCfg (tail buf xs : List Bool) : (machine M).Cfg :=
  ⟨some (loading M),(M.initial,none),store M (slot M M.input (xs.map M.inputAlphabet.symm)) tail buf⟩

def emitCfg (tail xs buf : List Bool) : (machine M).Cfg :=
  ⟨some (emitting M),(M.initial,none),store M (slot M M.output (xs.map M.outputAlphabet.symm)) tail buf⟩

def drainCfg (tail buf : List Bool) : (machine M).Cfg :=
  ⟨some (draining M),(M.initial,none),store M (fun _ => []) tail buf⟩

 theorem read_cons (b : Bool) (xs tail buf : List Bool) :
    (machine M).step (readCfg M (b::xs) tail buf)=some (readCfg M xs tail (b::buf)) := by
  simp [readCfg,TM2.step,code,readCode,TM2.stepAux,quote,clean,
    store_update_source,store_update_buffer]

 theorem read_nil (tail buf : List Bool) :
    (machine M).step (readCfg M [] tail buf)=some (loadCfg M tail buf []) := by
  simp [readCfg,loadCfg,TM2.step,code,readCode,TM2.stepAux,quote,clean,
    store_update_source,slot_nil,List.map_nil]

 theorem read_run (xs tail buf : List Bool) :
    Trace (machine M).step (xs.length+1) (readCfg M xs tail buf) (loadCfg M tail (xs.reverse++buf) []) := by
  induction xs generalizing buf with
  | nil => exact Trace.cons (read_nil M tail buf) (Trace.refl _)
  | cons b xs ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (read_cons M b xs tail buf) (ih (b::buf))

 theorem load_cons (b : Bool) (tail buf xs : List Bool) :
    (machine M).step (loadCfg M tail (b::buf) xs)=some (loadCfg M tail buf (b::xs)) := by
  simp [loadCfg,TM2.step,code,loadCode,TM2.stepAux,clean,
    store_update_buffer,store_update_local,slot_update,slot_self, List.map_cons]

 theorem load_nil (tail xs : List Bool) :
    (machine M).step (loadCfg M tail [] xs)=some ((body M tail).cfg (M.initialCfg xs)) := by
  simp [loadCfg,Embedding.cfg,body,Machine.initialCfg,TM2.step,code,loadCode,TM2.stepAux,
    clean,store_update_buffer,slot,Machine.single]

 theorem load_run (tail buf xs : List Bool) :
    Trace (machine M).step (buf.length+1) (loadCfg M tail buf xs)
      ((body M tail).cfg (M.initialCfg (buf.reverse++xs))) := by
  induction buf generalizing xs with
  | nil => exact Trace.cons (load_nil M tail xs) (Trace.refl _)
  | cons b bs ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (load_cons M b tail bs xs) (ih (b::xs))

 theorem emit_cons (b : Bool) (tail xs buf : List Bool) :
    (machine M).step (emitCfg M tail (b::xs) buf)=some (emitCfg M tail xs (b::true::buf)) := by
  simp [emitCfg,TM2.step,code,emitCode,TM2.stepAux,clean,
    store_update_local,store_update_buffer,slot_update,slot_self,List.map_cons]

 theorem emit_nil (tail buf : List Bool) :
    (machine M).step (emitCfg M tail [] buf)=some (drainCfg M tail (false::buf)) := by
  simp [emitCfg,drainCfg,TM2.step,code,emitCode,TM2.stepAux,clean,
    store_update_local,store_update_buffer,slot_nil,List.map_nil]

 theorem emit_run (tail xs buf : List Bool) :
    Trace (machine M).step (xs.length+1) (emitCfg M tail xs buf)
      (drainCfg M tail ((quote xs).reverse++buf)) := by
  induction xs generalizing buf with
  | nil => exact Trace.cons (emit_nil M tail buf) (Trace.refl _)
  | cons b xs ih =>
      simpa only [List.length_cons,quote,List.reverse_cons,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using
        Trace.cons (emit_cons M b tail xs buf) (ih (b::true::buf))

 theorem drain_cons (b : Bool) (tail buf : List Bool) :
    (machine M).step (drainCfg M tail (b::buf))=some (drainCfg M (b::tail) buf) := by
  simp [drainCfg,TM2.step,code,drainCode,TM2.stepAux,clean,
    store_update_source,store_update_buffer]

 theorem drain_nil (tail : List Bool) :
    (machine M).step (drainCfg M tail [])=some ((machine M).finalCfg tail) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    rcases k with k | k <;> try cases k
    all_goals simp [Machine.finalCfg,Machine.single,code,drainCode,
      TM2.stepAux,clean,store,machine,source,buffer]

 theorem drain_run (tail buf : List Bool) :
    Trace (machine M).step (buf.length+1) (drainCfg M tail buf) ((machine M).finalCfg (buf.reverse++tail)) := by
  induction buf generalizing tail with
  | nil => exact Trace.cons (drain_nil M tail) (Trace.refl _)
  | cons b bs ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (drain_cons M b tail bs) (ih (b::tail))

 theorem body_final (tail xs : List Bool) : (body M tail).cfg (M.finalCfg xs)=emitCfg M tail xs [] := rfl

 theorem run {xs zs : List Bool} {n : ℕ} (tail : List Bool)
    (h : Trace M.step n (M.initialCfg xs) (M.finalCfg zs)) :
    Trace (machine M).step (2*xs.length+3*zs.length+5+n)
      ((machine M).initialCfg (quote xs++tail)) ((machine M).finalCfg (quote zs++tail)) := by
  have hi : (machine M).initialCfg (quote xs++tail)=readCfg M xs tail [] := by
    apply cfg_ext <;> try rfl
    funext k
    rcases k with k | k <;> try cases k
    all_goals simp [Machine.initialCfg,Machine.single,readCfg,store,machine,source]
  rw [hi]
  have ha := read_run M xs tail []
  simp only [List.append_nil] at ha
  have hb := load_run M tail xs.reverse []
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at hb
  have hc := (body M tail).trace M.code (machine M).code (code_body M tail) h
  rw [body_final] at hc
  have hd := emit_run M tail zs []
  simp only [List.append_nil] at hd
  have he := drain_run M tail (quote zs).reverse
  simp only [List.reverse_reverse,List.length_reverse,quote_length] at he
  have hx := (((ha.trans hb).trans hc).trans hd).trans he
  convert hx using 1; omega

end Thread

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool} {f : α → β}

 noncomputable def thread (P : PolyProgram ea eb f) (ec : γ → List Bool) :
    PolyProgram (Binary.encodePair ea ec) (Binary.encodePair eb ec) (fun x => (f x.1,x.2)) where
  machine := Thread.machine P.machine
  time := 2*X+3*P.sizeBound+5+P.time
  outputs x := by
    obtain ⟨n, hn₀, ht₀⟩ := P.outputs x.1
    have h := Thread.run P.machine (ec x.2) ht₀
    refine ⟨_, ?_, h⟩
    have hn : (ea x.1).length ≤ (Binary.encodePair ea ec x).length := by
      simp only [Binary.encodePair_length]; omega
    have hl := (P.length_bound x.1).trans (polynomial_eval_mono P.sizeBound hn)
    have ht := hn₀.trans (polynomial_eval_mono P.time hn)
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    omega

end PolyProgram
end MetricKMedian.Complexity.FiniteComposition

end Inline_PCPInherited

end OAI
end


