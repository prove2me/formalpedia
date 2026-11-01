-- Prove2me | Definitions.Def_OAIQ053K033
-- name    : OAIQ053K033
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:00:39.691984+00:00
-- url     : https://prove2.me/theorems/66b14eb0-76d9-41dc-9955-81580cc69547
-- title:
--   Definitions bundle OAIQ053K033 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 91 declarations of OpenAI's Lean: 56 definitions, 1 inductive type or structure, 1 instance and 33 theorems. The definitions and types are `OAI.MetricKMedian.FixedBatch.nextAlive`, `OAI.MetricKMedian.Gaussian.IntegerProgram.Input.result`, `OAI.MetricKMedian.Gaussian.IntegerProgram.castRows`, `OAI.MetricKMedian.Gaussian.ListOperation.Desc`, `OAI.MetricKMedian.Gaussian.ListOperation.FrameValid`, `OAI.MetricKMedian.Gaussian.ListOperation.Frames`, `OAI.MetricKMedian.Gaussian.ListOperation.FramesValid`, `OAI.MetricKMedian.Gaussian.ListOperation.Input.encode`, `OAI.MetricKMedian.Gaussian.ListOperation.Input.raw`, `OAI.MetricKMedian.Gaussian.ListOperation.State`, `OAI.MetricKMedian.Gaussian.ListOperation.Up`, `OAI.MetricKMedian.Gaussian.ListOperation.body`, `OAI.MetricKMedian.Gaussian.ListOperation.desc`, `OAI.MetricKMedian.Gaussian.ListOperation.down`, `OAI.MetricKMedian.Gaussian.ListOperation.eState`, `OAI.MetricKMedian.Gaussian.ListOperation.eUp`, `OAI.MetricKMedian.Gaussian.ListOperation.ed`, `OAI.MetricKMedian.Gaussian.ListOperation.edata`, `OAI.MetricKMedian.Gaussian.ListOperation.ef`, `OAI.MetricKMedian.Gaussian.ListOperation.efs`, `OAI.MetricKMedian.Gaussian.ListOperation.er`, `OAI.MetricKMedian.Gaussian.ListOperation.ers`, `OAI.MetricKMedian.Gaussian.ListOperation.eslots`, `OAI.MetricKMedian.Gaussian.ListOperation.matrix`, `OAI.MetricKMedian.Gaussian.ListOperation.residual`, `OAI.MetricKMedian.Gaussian.ListOperation.returned`, `OAI.MetricKMedian.Gaussian.ListOperation.startProgram`, `OAI.MetricKMedian.Gaussian.ListOperation.up`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.Data`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.Input`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.Input.affine`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.Input.features`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.Input.large`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.Input.lawData`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.Input.raw`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.dummy`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.es`, `OAI.MetricKMedian.IntegerLaw.ListOperation.Data`, `OAI.MetricKMedian.IntegerLaw.ListOperation.Entry`, `OAI.MetricKMedian.IntegerLaw.ListOperation.Input.kernel` and 17 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Compression_AffineListCompiler`, `KMedian_Compression_AffineListOperations`, `KMedian_Compression_CompressionListStep`, `KMedian_Compression_GaussianBinaryProgram`, `KMedian_Compression_GaussianInputBounds`, `KMedian_Compression_GaussianListCompiler`, `KMedian_Compression_GaussianListMachine`, `KMedian_Compression_GaussianListOperations`, `KMedian_Compression_GaussianListSemantics`, `KMedian_Compression_GaussianListSize`, `KMedian_Compression_GaussianResidualHeight`, `KMedian_Compression_IntegerKernelProgram`, `KMedian_Geometry_FixedBatchTransition`, `KMedian_Geometry_GraphRunHeight`, `KMedian_Instance`, `KMedian_Optimization_IndexedInstanceLP`, `KMedian_Optimization_LPBinaryInput`, `KMedian_Optimization_TruncatedObjective`, `KMedian_Optimization_TruncatedOptimization`, `KMedian_Probability_BernoulliListOperations`, `KMedian_Probability_BernoulliRunHeight`, `KMedian_Probability_BernoulliStepProgram`, `KMedian_Process_BatchProposalProgram`, `KMedian_Process_CopyNextProgram`, `KMedian_Programs_CardinalRoundProgram`, `KMedian_Programs_PivotListProgram`, `KMedian_Sparse_SparseBindProgram`, `KMedian_Sparse_SparseBranchProgram`.
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundles `OAIQ053K013`, `OAIQ053K014`, `OAIQ053K015`, `OAIQ053K016`, `OAIQ053K017`, `OAIQ053K018`, `OAIQ053K019`, `OAIQ053K020` and `OAIQ053K021` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K040`, `OAIQ053K041` and `OAIQ053K042`; the statements `OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_frozen_bound_s53` and `OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_step_bound_s53`; the proofs of `OAI.MetricKMedian.SparseEnumeratedFixedBatch.actual_local_bound_s53`, `OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_frozen_bound_s53` and `OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_step_bound_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K013
import Definitions.Def_OAIQ053K014
import Definitions.Def_OAIQ053K015
import Definitions.Def_OAIQ053K016
import Definitions.Def_OAIQ053K017
import Definitions.Def_OAIQ053K018
import Definitions.Def_OAIQ053K019
import Definitions.Def_OAIQ053K020
import Definitions.Def_OAIQ053K021

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Gaussian.ListOperation
open Finset
universe uα uβ
variable {α : Type uα} {β : Type uβ}

def residual (row : Row) (p : ℕ) (rows : Rows) : Rows :=
  rows.map (reduce (coefficients row p) p)

def matrix {r n : ℕ} (A : Fin r → Fin n → ℚ) : Rows :=
  List.ofFn (fun i => List.ofFn (A i))

 theorem residual_matrix {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ) (p : Fin (n+1)) :
    residual (List.ofFn (A 0)) p.val (matrix (fun i : Fin r => A i.succ))=
      matrix (Gaussian.residual A p) := by
  simp only [residual,matrix,List.map_ofFn,Function.comp_def,coefficients_ofFn,reduce_ofFn]
  rfl

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianListCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Binary.PolyProgram Function
abbrev er : Row → List Bool := encodeList Ratio.encode
abbrev ers : Rows → List Bool := encodeList er
abbrev ef : ℕ × Row → List Bool := encodePair Nat.bits er
abbrev eslots : List Unit → List Bool := encodeList eu

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianListMachine
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Binary.PolyProgram Function
abbrev Frames := List Frame
abbrev Desc := (List Unit × Rows) × Frames
abbrev Up := Row × Frames
abbrev State := Desc ⊕ Up
abbrev efs := encodeList ef
abbrev edata := encodePair eslots ers
abbrev ed := encodePair edata efs
abbrev eUp := encodePair er efs
abbrev eState : State → List Bool := encodeLoop eUp ed

def down (d : Desc) : Row ⊕ State :=
  if d.1.2.isEmpty then .inr (.inr (basis d.1.1,d.2))
  else if d.1.1.isEmpty then .inr (.inr ([],d.2))
  else
    let row := d.1.2.head?.getD []
    let p := pivot row
    if p < row.length then
      .inr (.inl ((d.1.1.tail,residual row p d.1.2.tail),(p,row)::d.2))
    else .inr (.inl ((d.1.1,d.1.2.tail),d.2))

def up (u : Up) : Row ⊕ State :=
  if u.2.isEmpty then .inl u.1
  else
    let f := u.2.head?.getD (0,[])
    .inr (.inr (lift f.2 f.1 u.1,u.2.tail))

def body : State → Row ⊕ State := Sum.elim down up

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianResidualHeight
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.RationalLaw.scaledFeatures_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Gaussian
open Finset

 theorem combination_height (R H L : ℕ) (q z : Fin R → ℚ) (U : Fin R → ℤ)
    (w : Fin R) (hw : U w ≠ 0) (hU : ∀ i, |U i| ≤ (2:ℤ)^H)
    (hz : ∀ i, z i=(U i:ℚ)/(U w:ℚ))
    (hnum : ∀ i, |(q i).num| ≤ (2:ℤ)^L)
    (hden : ∀ i, ((q i).den:ℤ) ≤ (2:ℤ)^L) :
    |(∑ i, q i*z i).num| ≤ (2:ℤ)^(R+H+L*(R+1)) ∧
      (((∑ i, q i*z i).den:ℕ):ℤ) ≤ (2:ℤ)^(R+H+L*(R+1)) := by
  let V := RationalScaling.numerator q
  let D := RationalScaling.denominator q
  let a : ℤ := ∑ i, V i*U i
  let b : ℤ := D*U w
  have hD : 0 < D := RationalScaling.denominator_pos q
  have hDc : (D:ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hwc : (U w:ℚ) ≠ 0 := by exact_mod_cast hw
  have hb : b ≠ 0 := mul_ne_zero hD.ne' hw
  have hV : ∀ i, |V i| ≤ (2:ℤ)^(L*(R+1)) := by
    intro i
    simpa only [Fintype.card_fin] using RationalScaling.numerator_bound q L hnum hden i
  have hDb : D ≤ (2:ℤ)^(L*R) := by
    simpa only [Fintype.card_fin] using RationalScaling.denominator_bound q L hden
  have he : (∑ i, q i*z i)=(a:ℚ)/(b:ℚ) := by
    have hq : ∀ i, q i=(V i:ℚ)/(D:ℚ) := by
      intro i
      apply (eq_div_iff hDc).mpr
      exact (RationalScaling.numerator_cast q i).symm
    simp only [a,b,Int.cast_mul,Int.cast_sum,hq,hz]
    rw [Finset.sum_div]
    apply sum_congr rfl
    intro i _
    ring
  have ha : |a| ≤ (2:ℤ)^(R+H+L*(R+1)) := by
    calc
      _ ≤ ∑ i : Fin R, |V i*U i| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin R, (2:ℤ)^(L*(R+1))*(2:ℤ)^H :=
        sum_le_sum (fun i _ => by rw [abs_mul]; exact mul_le_mul (hV i) (hU i) (abs_nonneg _) (by positivity))
      _ = (R:ℤ)*(2:ℤ)^(L*(R+1)+H) := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,pow_add]
      _ ≤ (2:ℤ)^R*(2:ℤ)^(L*(R+1)+H) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (Nat.lt_two_pow_self (n:=R)).le
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hbH : |b| ≤ (2:ℤ)^(R+H+L*(R+1)) := by
    calc
      _ = D*|U w| := by simp only [b,abs_mul,abs_of_pos hD]
      _ ≤ (2:ℤ)^(L*R)*(2:ℤ)^H := mul_le_mul hDb (hU w) (abs_nonneg _) (by positivity)
      _ = (2:ℤ)^(L*R+H) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by nlinarith)
  rw [he]
  exact ratio_num_den_bound a b hb _ ha hbH

end MetricKMedian.Gaussian
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianListSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Binary.PolyProgram Function

def FrameValid (N H : ℕ) (f : Frame) : Prop :=
  f.1  ≤  N ∧ f.2.length  ≤  N ∧ ∀ q∈f.2, HasHeight q H
def FramesValid (N H : ℕ) (fs : Frames) : Prop := ∀ f∈fs, FrameValid N H f

 theorem slots_size (n : ℕ) : (eslots (List.replicate n ())).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,EncodedList.cons_length,eu,List.length_nil,ih]; omega

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianInputBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Finset Polynomial

def Input.raw (I : Input) : List Unit × Rows :=
  (List.replicate I.cols (),matrix (values I.data))
abbrev Input.encode (I : Input) := edata I.raw

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianListSemantics
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Finset

def desc (r n : ℕ) (A : RatMatrix r n) (fs : Frames) : State :=
  .inl ((List.replicate n (),matrix (values A)),fs)
def returned (r n : ℕ) (A : RatMatrix r n) (fs : Frames) : State :=
  .inr (kernelList r n A,fs)

 theorem down_base (n : ℕ) (A : RatMatrix 0 n) (fs : Frames) :
    body (desc 0 n A fs)=.inr (returned 0 n A fs) := by
  simp only [desc,body,Sum.elim_inl,down,matrix,List.ofFn_zero,List.isEmpty_nil,ite_true]
  rw [basis_ofFn]
  simp only [returned,kernelList,kernelVector,Vector.getElem_ofFn]

 theorem down_pivot {r n : ℕ} (A : RatMatrix (r+1) (n+1)) (fs : Frames)
    (h : (univ.filter (fun j => values A 0 j ≠ 0)).Nonempty) :
    let p := (univ.filter (fun j => values A 0 j ≠ 0)).min' h
    body (desc (r+1) (n+1) A fs)=
      .inr (desc r n (tabulate (Gaussian.residual (values A) p)) ((p.val,List.ofFn (values A 0))::fs)) := by
  dsimp only
  let p := (univ.filter (fun j => values A 0 j ≠ 0)).min' h
  have hm : matrix (values A)=List.ofFn (values A 0)::matrix (fun i : Fin r => values A i.succ) := List.ofFn_succ
  simp only [desc,body,Sum.elim_inl,down,hm,List.isEmpty_cons,Bool.false_eq_true,ite_false,List.replicate_succ,List.head?_cons,Option.getD_some,List.tail_cons]
  simp only [pivot_ofFn _ h,List.length_ofFn,residual_matrix,values_tabulate]
  exact ite_eq_left p.isLt

 theorem down_skip {r n : ℕ} (A : RatMatrix (r+1) (n+1)) (fs : Frames)
    (h : ¬(univ.filter (fun j => values A 0 j ≠ 0)).Nonempty) :
    body (desc (r+1) (n+1) A fs)=
      .inr (desc r (n+1) (tabulate (fun i j => values A i.succ j)) fs) := by
  have hm : matrix (values A)=List.ofFn (values A 0)::matrix (fun i : Fin r => values A i.succ) := List.ofFn_succ
  simp only [desc,body,Sum.elim_inl,down,hm,List.isEmpty_cons,Bool.false_eq_true,ite_false,List.replicate_succ,List.head?_cons,Option.getD_some,List.tail_cons]
  simp only [pivot_ofFn_zero _ h,List.length_ofFn,lt_self_iff_false,ite_false,values_tabulate]

 theorem return_pivot {r n : ℕ} (A : RatMatrix (r+1) (n+1)) (fs : Frames)
    (h : (univ.filter (fun j => values A 0 j ≠ 0)).Nonempty) :
    let p := (univ.filter (fun j => values A 0 j ≠ 0)).min' h
    body (returned r n (tabulate (Gaussian.residual (values A) p)) ((p.val,List.ofFn (values A 0))::fs))=
      .inr (returned (r+1) (n+1) A fs) := by
  dsimp only
  simp only [returned,body,Sum.elim_inr,up,List.isEmpty_cons,Bool.false_eq_true,ite_false,List.head?_cons,Option.getD_some,List.tail_cons]
  simp only [kernelList,lift_ofFn,kernelVector,dite_eq_left h,Vector.getElem_ofFn]

 theorem return_skip {r n : ℕ} (A : RatMatrix (r+1) (n+1)) (fs : Frames)
    (h : ¬(univ.filter (fun j => values A 0 j ≠ 0)).Nonempty) :
    returned r (n+1) (tabulate (fun i j => values A i.succ j)) fs=returned (r+1) (n+1) A fs := by
  simp only [returned,kernelList,kernelVector,dite_eq_right h]

 theorem finish (r n : ℕ) (A : RatMatrix r n) :
    body (returned r n A [])=.inl (kernelList r n A) := rfl

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianBinaryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Binary.PolyProgram Polynomial

noncomputable def startProgram : PolyProgram Input.encode eState (fun I : Input => desc I.rows I.cols I.data []) := by
  let raw : PolyProgram Input.encode edata Input.raw := (identity edata).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  exact ((raw.fanout (constant Input.encode efs [])).comp (injectLeft eUp ed)).congr _ (fun _ => rfl)

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_IntegerKernelProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Gaussian.IntegerProgram
open Binary Binary.PolyProgram
def castRows (vs : Rows) : ListOperation.Rows := vs.map (List.map (fun z : ℤ => (z:ℚ)))

theorem castRows_ofFn {r n : ℕ} (V : Fin r → Fin n → ℤ) :
    castRows (List.ofFn (fun i => List.ofFn (V i)))=ListOperation.matrix (fun i j => (V i j:ℚ)) := by
  simp only [castRows,List.map_ofFn,Function.comp_def,ListOperation.matrix]

def Input.result (I : Input) : Row := List.ofFn (computedIntegerKernel I.r I.n I.V)

end MetricKMedian.Gaussian.IntegerProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_AffineListOperations
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.IntegerLaw.ListOperation
open Binary Gaussian
open Finset
abbrev es := Gaussian.ListOperation.eslots
abbrev Data := List Unit × (Row × Rows)
abbrev Entry := ℕ × (ℤ × Row)

def entries (x : Data) : List Entry :=
  let zs := x.2.1.zip x.2.2
  (List.range zs.length).zip zs

def active (x : Data) : List Entry := (entries x).filter (fun e => decide (e.2.1≠0))
def activeRows (x : Data) : Gaussian.IntegerProgram.Rows :=
  (active x).map (fun _ => 1) :: (List.range x.1.length).map (fun j => (active x).map (fun e => e.2.2[j]?.getD 0))
def activeData (x : Data) : List Unit × Rows :=
  ((active x).map (fun _ => ()),activeRows x)

def full (x : Data) (z : Row) : Row :=
  let zs := ((active x).map Prod.fst).zip z
  (List.range x.2.1.length).map (extend zs)

def Input.raw (I : Input) : Data :=
  (List.replicate I.d (),(List.ofFn I.μ.numerator,List.ofFn (fun i => List.ofFn (I.v i))))

def Input.kernel (I : Input) : Gaussian.IntegerProgram.Input :=
  ⟨I.d+1,I.μ.support.card,activeMatrix I.μ I.v,I.large⟩

theorem entries_raw (I : Input) : entries I.raw=List.ofFn (fun i : Fin I.n =>
    (i.val,(I.μ.numerator i,List.ofFn (I.v i)))) := by
  simp only [entries,Input.raw,Gaussian.ListOperation.zip_ofFn,List.length_ofFn,range_ofFn]

theorem active_raw (I : Input) : active I.raw=List.ofFn (fun j : Fin I.μ.support.card =>
    let i := ((I.μ.support.orderIsoOfFin rfl) j).val
    (i.val,(I.μ.numerator i,List.ofFn (I.v i)))) := by
  rw [active,entries_raw,List.ofFn_eq_map,List.filter_map]
  exact EncodingLists.map_filter_enum _ (fun i => I.μ.numerator i≠0)

theorem activeRows_raw (I : Input) : activeRows I.raw=
    List.ofFn (fun j => List.ofFn (activeMatrix I.μ I.v j)) := by
  rw [activeRows,active_raw]
  simp only [Input.raw,List.length_replicate,List.map_ofFn,Function.comp_def]
  rw [indices_ofFn,List.map_ofFn,List.ofFn_succ]
  congr 1
  congr 1
  funext j
  simp only [Function.comp_apply,Gaussian.ListOperation.get_ofFn]
  rfl

theorem activeData_raw (I : Input) : activeData I.raw=I.kernel.raw := by
  simp only [activeData,activeRows_raw,active_raw,List.map_ofFn,Function.comp_def,List.ofFn_const,
    Input.kernel,Gaussian.IntegerProgram.Input.raw]

theorem full_raw (I : Input) :
    full I.raw (List.ofFn (Gaussian.computedIntegerKernel (I.d+1) I.μ.support.card (activeMatrix I.μ I.v)))=
      List.ofFn (computedAffineKernel I.μ I.v) := by
  rw [full,active_raw]
  simp only [List.map_ofFn,Function.comp_def,Gaussian.ListOperation.zip_ofFn]
  simp only [Input.raw,List.length_ofFn,indices_ofFn,List.map_ofFn,Function.comp_def,extend_ofFn,
    computedAffineKernel,Vector.getElem_ofFn]

end MetricKMedian.IntegerLaw.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_AffineListCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.IntegerLaw.ListOperation
open Binary Binary.PolyProgram Function

abbrev ez := encodePair Nat.bits Signed.encode

end MetricKMedian.IntegerLaw.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_PivotListProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.IntegerLaw.ListPivot
open Binary Binary.PolyProgram Function Finset
abbrev ee := encodePair Signed.encode Signed.encode
abbrev ees := encodeList ee

theorem least_ofFn {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ)
    (h : (positiveSet z).Nonempty) :
    least (List.ofFn (fun i => (μ.numerator i,z i)))=leastRatio μ z h := by
  apply LPBinary.minimum_eq_finset
  intro q
  simp only [List.mem_map,List.mem_filter,List.mem_ofFn,decide_eq_true_eq,mem_image,positiveSet,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨e,⟨⟨i,rfl⟩,hi⟩,rfl⟩
    exact ⟨i,hi,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨(μ.numerator i,z i),⟨⟨i,rfl⟩,hi⟩,rfl⟩

theorem pivot_ofFn {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ)
    (h : (positiveSet z).Nonempty) :
    pivot (List.ofFn (fun i => (μ.numerator i,z i)))=(computedPivot μ z h).val := by
  unfold pivot
  rw [least_ofFn μ z h]
  let p := computedPivot μ z h
  apply (List.findIdx_eq (by simpa only [List.length_ofFn] using p.isLt)).mpr
  constructor
  · have hp := mem_filter.mp (min'_mem (pivotSet μ z h) (pivotSet_nonempty μ z h))
    simpa only [List.getElem_ofFn,decide_eq_true_eq,ratio,IntegerLaw.ratio] using ⟨(mem_filter.mp hp.1).2,hp.2⟩
  · intro j hj
    simp only [List.getElem_ofFn,decide_eq_false_iff_not]
    intro hp
    have hm : p ≤ (⟨j,Nat.lt_trans hj p.isLt⟩ : Fin n) := min'_le (pivotSet μ z h) _
      (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hp.1⟩,hp.2⟩)
    exact (not_le_of_gt hj) hm

theorem update_ofFn {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ)
    (h : (positiveSet z).Nonempty) (hzsum : ∑ i, z i=0) :
    update (μ.denominator,List.ofFn μ.numerator) (List.ofFn z)=
      let ν := eliminateAt μ z (computedPivot μ z h) (computedPivot_spec μ z h).1 (computedPivot_spec μ z h).2 hzsum
      (ν.denominator,List.ofFn ν.numerator) := by
  simp only [update,Gaussian.ListOperation.zip_ofFn,pivot_ofFn μ z h,Gaussian.ListOperation.get_ofFn,List.map_ofFn,
    Function.comp_def,eliminateAt,Vector.getElem_ofFn]

end MetricKMedian.IntegerLaw.ListPivot
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_CompressionListStep
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.IntegerLaw.trim_denominator _root_.OAI.MetricKMedian.IntegerLaw.trim_numerator _root_.OAI.MetricKMedian.IntegerLaw.trim_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function Finset
abbrev es := Gaussian.ListOperation.eslots
abbrev Data := List Unit × (LawData × Rows)

structure Input where
  n : ℕ
  d : ℕ
  μ : IntegerLaw (Fin n)
  v : Fin n → Fin d → ℤ

def Input.lawData (I : Input) : LawData := (I.μ.denominator,List.ofFn I.μ.numerator)
def Input.features (I : Input) : Rows := List.ofFn (fun i => List.ofFn (I.v i))
def Input.raw (I : Input) : Data := (List.replicate I.d (),(I.lawData,I.features))

def Input.large (I : Input) : Prop := I.d+1 < I.μ.support.card
instance instDecidablePredInputLarge : DecidablePred Input.large := fun _ => inferInstanceAs (Decidable (_<_))
def Input.affine (I : Input) (h : I.large) : ListOperation.Input := ⟨I.n,I.d,I.μ,I.v,h⟩

def dummy : Input := ⟨3,0,⟨3,by norm_num,(fun _ => 1),by intros; norm_num,by norm_num⟩,fun _ i => Fin.elim0 i⟩
theorem dummy_large : dummy.large := by
  change 1 < (Finset.univ.filter (fun _ : Fin 3 => (1:ℤ) ≠ 0)).card
  norm_num

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_FixedBatchTransition
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic

variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

noncomputable def nextAlive (D : Actions I E) (x g : ℝ) (d : I → ℝ)
    (S : Finset I) (A : Finset E) : Finset I :=
  if h : (internal D S A).Nonempty then
    retained (coefficient x (mass g S)) (d (D.source h.choose)) d (physical D S A)
  else physical D S A

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_GraphRunHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseGraph
open Binary
variable {n m : ℕ}

theorem edge_height (G : Graph n m) (h : Fin n) (i : Fin m) : HasHeight (edge G h i) 0 := by
  unfold edge
  split_ifs
  · exact HasHeight.one 0
  · exact HasHeight.zero 0

theorem features_height (G : Graph n m) (a : Fin (n*m+(n*m)*(n*m))) : HasHeight (features G a) 0 := by
  unfold features edgeCode
  generalize finSumFinEquiv.symm a=z
  cases z with
  | inl i => exact edge_height _ _ _
  | inr ij => exact (edge_height _ _ _).mul (edge_height _ _ _)

end MetricKMedian.SparseGraph
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Instance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset

namespace Instance

theorem feasible_nonempty (I : Instance) : (feasibleSets I).Nonempty := by
  obtain ⟨i,hi⟩ := I.facilities_nonempty
  refine ⟨{i},mem_filter.mpr ⟨mem_powerset.mpr ?_,singleton_nonempty _,?_⟩⟩
  · exact singleton_subset_iff.mpr hi
  · simpa only [card_singleton] using I.k_pos

theorem optimum_attained (I : Instance) :
    ∃ S, S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k ∧ cost I S=optimum I := by
  have hS := I.feasible_nonempty
  have hm := min'_mem ((feasibleSets I).image (cost I)) (hS.image _)
  obtain ⟨S,hSf,he⟩ := mem_image.mp hm
  obtain ⟨hsub,hne,hcard⟩ := (I.mem_feasible S).mp hSf
  exact ⟨S,hsub,hne,hcard,by rw [optimum,dite_eq_left hS]; exact he⟩

end Instance
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_TruncatedObjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset
variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem subgradient (d : κ → ι → ℚ) (y z : ι → ℚ) (H : ℚ) :
    objective d y H-objective d z H ≤ ∑ i, gradient d y H i*(y i-z i) := by
  have hh := sum_le_sum (fun j (_ : j ∈ (univ:Finset κ)) =>
    FractionalDual.gradient_spec (truncated d H j) y z H)
  rw [sum_sub_distrib] at hh
  apply hh.trans_eq
  rw [sum_comm]
  exact sum_congr rfl (fun i _ => by rw [← sum_mul]; rfl)

theorem gradient_abs_bound (d : κ → ι → ℚ) (y : ι → ℚ) (H : ℚ)
    (hH : 1 ≤ H) (hd : ∀ j i, 0 ≤ d j i) (i : ι) :
    |gradient d y H i| ≤ (Fintype.card κ:ℚ)*H := by
  unfold gradient
  calc
    _ ≤ ∑ j, |FractionalDual.gradient (truncated d H j) y H i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : κ, H := sum_le_sum (fun j _ => FractionalDual.gradient_bound _ _ _
      (by linarith) (truncated_bounds d H hH hd j) i)
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]

theorem gradient_sq_bound (d : κ → ι → ℚ) (y : ι → ℚ) (H : ℚ)
    (hH : 1 ≤ H) (hd : ∀ j i, 0 ≤ d j i) :
    (∑ i, (gradient d y H i)^2) ≤ (Fintype.card ι:ℚ)*((Fintype.card κ:ℚ)*H)^2 := by
  calc
    _ ≤ ∑ _i : ι, ((Fintype.card κ:ℚ)*H)^2 := sum_le_sum (fun i _ => by
      have hh := gradient_abs_bound d y H hH hd i
      have hh' := mul_self_le_mul_self (abs_nonneg (gradient d y H i)) hh
      simpa only [← sq, sq_abs] using hh')
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]

theorem objective_le_assignment (d : κ → ι → ℚ) (y : ι → ℚ) (x : κ → ι → ℚ)
    (H : ℚ) (hx : ∀ j i, 0 ≤ x j i ∧ x j i ≤ y i) (hs : ∀ j, ∑ i, x j i=1) :
    objective d y H ≤ ∑ j, ∑ i, x j i*truncated d H j i :=
  sum_le_sum (fun j _ => FractionalDual.value_le_assignment _ _ _ _ (hx j) (hs j))

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_TruncatedOptimization
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
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

theorem optimize_spec (d : Fin m → Fin n → ℚ) (r k H : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hH : 0 < H) (hd : ∀ j i, 0 ≤ d j i)
    (z : Fin n → ℚ) (hz : feasible (k:ℚ) z) :
    feasible (k:ℚ) (point (optimize d r k H hr hk hH)) ∧
      objective d (point (optimize d r k H hr hk hH)) H ≤ objective d z H+1/(r:ℚ) := by
  let T := steps (n:=n) (m:=m) r k H
  let : NeZero T := ⟨(steps_pos r k H hr hk hH).ne'⟩
  let v := trajectory (k:ℚ) (rate (n:=n) (m:=m) r H)
    (fun y => gradient d y H) (initial (k:ℚ))
  let a := Preparation.firstNearest (univ:Finset (Fin T))
    (fun t => objective d (point (v t.val)) H) univ_nonempty
  have hkq : (0:ℚ) < k := by exact_mod_cast hk
  have hHq : (1:ℚ) ≤ H := by exact_mod_cast hH
  have hstart := initial_feasible (n:=n) (k:ℚ) hkq.le
  have hh := Preparation.firstNearest_spec (univ:Finset (Fin T))
    (fun t => objective d (point (v t.val)) H) univ_nonempty
  change feasible (k:ℚ) (point (v a.val)) ∧
    objective d (point (v a.val)) H ≤ objective d z H+1/(r:ℚ)
  refine ⟨trajectory_feasible _ _ _ _ hkq hstart _,?_⟩
  obtain ⟨t,ht,htc⟩ := exists_accurate (fun y => objective d y H) (fun y => gradient d y H)
    (k:ℚ) (rate (n:=n) (m:=m) r H) (gradSize (n:=n) (m:=m) H:ℚ) (1/(r:ℚ))
    hkq (rate_pos r H hr hH) (initial (k:ℚ)) hstart z hz
    (fun y _ => subgradient d y z H)
    (fun y _ => by
      simpa only [gradSize,Fintype.card_fin,Nat.cast_mul,Nat.cast_pow] using
        gradient_sq_bound d y H hHq hd)
    T (steps_pos r k H hr hk hH) (iteration_bound r k H hr hH _ z hstart hz)
  exact (hh.2 ⟨t,mem_range.mp ht⟩ (mem_univ _)).trans htc

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_IndexedInstanceLP
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset
namespace Instance

theorem indexed_integral (I : Instance) (S : Finset (Fin I.n))
    (hSF : S ⊆ I.facilities) (hS : S.Nonempty) :
    ∃ T : Finset (Fin I.facilities.card), T.Nonempty ∧ T.card=S.card ∧
      ∃ a : Fin I.clients.card → Fin I.facilities.card, (∀ j, a j ∈ T) ∧
        (∑ j, I.indexedDistance j (a j))=rationalCost I S := by
  classical
  let f := I.facilities.orderEmbOfFin rfl
  let T := S.preimage f f.injective.injOn
  have hT : T.card=S.card := by
    rw [card_preimage]
    change ({x ∈ S | x ∈ Set.range (I.facilities.orderEmbOfFin rfl)}).card=S.card
    simp only [range_orderEmbOfFin]
    congr 1
    exact filter_eq_self.mpr hSF
  have hTn : T.Nonempty := card_pos.mp (by rw [hT]; exact card_pos.mpr hS)
  have each : ∀ j : Fin I.clients.card, ∃ i : Fin I.facilities.card,
      i ∈ T ∧ I.indexedDistance j i=rationalNearest I (I.clients.orderEmbOfFin rfl j) S := by
    intro j
    obtain ⟨i,hi,hd⟩ := I.rationalNearest_attained (I.clients.orderEmbOfFin rfl j) S hS
    let b : ↥I.facilities := ⟨i,hSF hi⟩
    let ai := (I.facilities.orderIsoOfFin rfl).symm b
    have he : f ai=i := congrArg Subtype.val ((I.facilities.orderIsoOfFin rfl).apply_symm_apply b)
    refine ⟨ai,mem_preimage.mpr ?_,?_⟩
    · rwa [he]
    · change I.distance _ (f ai)=_
      rw [he,hd]
  choose a ha hd using each
  refine ⟨T,hTn,hT,a,ha,?_⟩
  calc
    _ = ∑ j : Fin I.clients.card, rationalNearest I (I.clients.orderEmbOfFin rfl j) S :=
      sum_congr rfl (fun j _ => hd j)
    _ = ∑ j : ↥I.clients, rationalNearest I j.val S :=
      (I.clients.orderIsoOfFin rfl).toEquiv.sum_comp (fun j => rationalNearest I j.val S)
    _ = _ := sum_coe_sort I.clients (fun j => rationalNearest I j S)

end Instance
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_LPBinaryInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.LPBinary
open Binary Polynomial Finset

namespace Input
def rows (I : Input) : Rows := List.ofFn (fun j => List.ofFn (I.distance j))
end Input

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.SparseBernoulli.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly
abbrev er := encodeList encodeBool

end MetricKMedian.SparseBernoulli.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliRunHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.SparseBernoulli
open Binary
variable {n d : ℕ}

theorem features_height (q : Fin n → Bool) (a : Fin ((n+1)^d)) : HasHeight (features q a) 0 := by
  unfold features monomial
  rw [ListOperation.flag_product]
  split_ifs
  · exact HasHeight.one 0
  · exact HasHeight.zero 0

end MetricKMedian.SparseBernoulli
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBranchProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.PolyProgram Function
variable {α γ : Type}

theorem branchLaw_ofFn {n : ℕ} (μ : IntegerLaw (Fin n)) (p : Fin n → ℚ)
    (hp : ∀ i, 0≤p i ∧ p i≤1) :
    branchLawData ((μ.denominator,List.ofFn μ.numerator),List.ofFn p)=
      ((IntegerBranching.branch μ p hp).denominator,
        List.ofFn ((IntegerBranching.branch μ p hp).reindex finProdFinEquiv).numerator) := by
  simp only [branchLawData,IntegerList.denominator_ofFn,IntegerList.numerators_ofFn,
    Gaussian.ListOperation.zip_ofFn,List.flatMap_def,List.map_ofFn,Function.comp_def]
  congr 1
  rw [show ((IntegerBranching.branch μ p hp).reindex finProdFinEquiv).numerator=
    (fun i => μ.numerator (finProdFinEquiv.symm i).1 *
      IntegerBranching.branchNumerator p (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) from by
      funext i; simp only [IntegerLaw.reindex,IntegerBranching.branch,Vector.getElem_ofFn]]
  rw [two_expand (fun i b => μ.numerator i * IntegerBranching.branchNumerator p i b)]
  simp only [IntegerBranching.branchNumerator,show (1:Fin 2)≠0 from by decide,ite_true,ite_false]

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliStepProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseBernoulli.Program
open Binary Binary.PolyProgram Function
abbrev er := ListOperation.er

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBindProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.Automatic Binary.Automatic.Poly Finset

variable {α β A : Type}

 theorem weights_law {n : ℕ} (μ : IntegerLaw (Fin n)) :
    weights (μ.denominator,List.ofFn μ.numerator)=List.ofFn μ.rational.weight := by
  simp only [weights,List.map_ofFn,Function.comp_def,IntegerLaw.rational]

 theorem scaling_numerator_equiv {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (w : ι → ℚ) (j : κ) :
    RationalScaling.numerator (fun j => w (e.symm j)) j=RationalScaling.numerator w (e.symm j) := by
  apply Int.cast_injective (α:=ℚ)
  rw [RationalScaling.numerator_cast,RationalScaling.numerator_cast,scaling_denominator_equiv]

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_BatchProposalProgram
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.RationalBatchData.ProposalProgram
open Finset FixedBatch Binary Binary.PolyProgram
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
variable {C : Type} (I : C → Type) [∀ c, LinearOrder (I c)] [∀ c, Fintype (I c)]

variable {I}

def Input.batch (x : Input I) : SparsePhysicalBatch.Program.Input where
  n := Fintype.card (HeavyAction (graph x.G) (heavySet (graphMass x.G x.g) x.b))
  Z := (balanced (heavy (graph x.G) (heavySet (graphMass x.G x.g) x.b)) x.Δ).map x.enumActions.symm.toEmbedding
  C := fun i => (conflicts (heavy (graph x.G) (heavySet (graphMass x.G x.g) x.b)) x.Δ (x.enumActions i)).map x.enumActions.symm.toEmbedding
  p := x.p
  q := fun i => bias (graphMass x.G x.g) x.p x.φ (heavyParent (graph x.G) _ (x.enumActions i))
  hp := ⟨x.hp,by have h := mul_nonneg x.hp x.hφ; nlinarith only [h,x.hupper]⟩
  hq := fun _ => bias_probability (graphMass x.G x.g) x.hp x.hφ x.hupper _
end MetricKMedian.RationalBatchData.ProposalProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_CardinalRoundProgram
attribute [-simp] _root_.OAI.MetricKMedian.RationalSignedTerminal.point_state _root_.OAI.MetricKMedian.SparseTargetSubset.point_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseCardinalRounding.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
abbrev qr := encodeList Ratio.encode

def weightedInput (x : Input) : RoundingProgram.Input false :=
  ⟨x.n,fun _ => 1,Vector.ofFn x.p,fun _ _ => by norm_num,fun i => by
    simpa only [RationalWeightedStep.point,Vector.getElem_ofFn] using x.feasible i⟩
end MetricKMedian.SparseCardinalRounding.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CopyNextProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.RationalPhysicalKernel.CopyNext
open Binary Binary.Automatic Binary.Automatic.Poly Finset FixedBatch
open CopyList
open CopyGraphProgram (rank_owner)
open SparseGraph.ListOperation (Row Table setView indices)
local instance instLinearOrderCopyFin_r2d82ab_1 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
local instance instLinearOrderSubtypeCopyFinMemFinset {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : LinearOrder ↥A := activeOrder A

end MetricKMedian.RationalPhysicalKernel.CopyNext
end

end OAI
end


