-- Prove2me | Definitions.Def_OAIQ035K031
-- name    : OAIQ035K031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:59:42.939093+00:00
-- url     : https://prove2.me/theorems/0dbac0cf-a535-4d45-8c7c-4b70d3ba9e58
-- title:
--   Definitions bundle OAIQ035K031 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 83 declarations of OpenAI's Lean: 47 definitions, 2 inductive types or structures, 1 instance and 33 theorems. The definitions and types are `OAI.MetricKMedian.Gaussian.IntegerProgram.Input.result`, `OAI.MetricKMedian.Gaussian.ListOperation.Audit`, `OAI.MetricKMedian.Gaussian.ListOperation.Input.encode`, `OAI.MetricKMedian.Gaussian.ListOperation.Input.result`, `OAI.MetricKMedian.Gaussian.ListOperation.eState`, `OAI.MetricKMedian.Gaussian.ListOperation.eUp`, `OAI.MetricKMedian.Gaussian.ListOperation.ed`, `OAI.MetricKMedian.Gaussian.ListOperation.edata`, `OAI.MetricKMedian.Gaussian.ListOperation.ef`, `OAI.MetricKMedian.Gaussian.ListOperation.efs`, `OAI.MetricKMedian.Gaussian.ListOperation.er`, `OAI.MetricKMedian.Gaussian.ListOperation.ers`, `OAI.MetricKMedian.Gaussian.ListOperation.eslots`, `OAI.MetricKMedian.Gaussian.ListOperation.kernelList`, `OAI.MetricKMedian.Gaussian.ListOperation.returned`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.Data`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.Input`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.Input.affine`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.Input.features`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.Input.large`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.Input.lawData`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.Input.raw`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.QData`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.RationalInput`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.RationalInput.features`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.RationalInput.integer`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.RationalInput.lawData`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.RationalInput.raw`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.dummy`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.eqm`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.eqr`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.es`, `OAI.MetricKMedian.IntegerLaw.ListOperation.Data`, `OAI.MetricKMedian.IntegerLaw.ListOperation.Entry`, `OAI.MetricKMedian.IntegerLaw.ListOperation.Input.raw`, `OAI.MetricKMedian.IntegerLaw.ListOperation.active`, `OAI.MetricKMedian.IntegerLaw.ListOperation.entries`, `OAI.MetricKMedian.IntegerLaw.ListOperation.es`, `OAI.MetricKMedian.IntegerLaw.ListOperation.ez`, `OAI.MetricKMedian.IntegerLaw.ListOperation.full` and 9 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Compression_AffineListCompiler`, `KMedian_Compression_AffineListOperations`, `KMedian_Compression_CompressionListStep`, `KMedian_Compression_GaussianBinaryProgram`, `KMedian_Compression_GaussianInputBounds`, `KMedian_Compression_GaussianListCompiler`, `KMedian_Compression_GaussianListMachine`, `KMedian_Compression_GaussianListSemantics`, `KMedian_Compression_GaussianListSize`, `KMedian_Compression_GaussianResidualHeight`, `KMedian_Compression_IntegerKernelProgram`, `KMedian_Geometry_ComputedRationalCompression`, `KMedian_Process_RoundingCoordinateHeight`, `KMedian_Process_RoundingListOperations`, `KMedian_Process_RoundingUniformStep`, `KMedian_Programs_GraphLawProgram`, `KMedian_Programs_PivotListProgram`, `KMedian_Programs_RationalFeatureProgram`, `KMedian_Rounding_RationalCopyTransition`, `KMedian_Rounding_RationalSignedStep`, `KMedian_Rounding_RationalWeightedInvariants`, `KMedian_Rounding_WeightedGridInvariant`, `KMedian_Sparse_SparseIterationHeight`.
--
--   **Imports.** It imports the bundles `OAIQ035K014`, `OAIQ035K015`, `OAIQ035K016`, `OAIQ035K017`, `OAIQ035K018`, `OAIQ035K019` and `OAIQ035K020` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K040`, `OAIQ035K041` and `OAIQ035K062`; the proof of `OAI_MetricKMedian_SparseBernoulli_count_variance`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K014
import Definitions.Def_OAIQ035K015
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K017
import Definitions.Def_OAIQ035K018
import Definitions.Def_OAIQ035K019
import Definitions.Def_OAIQ035K020

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianListCompiler
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
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianListMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Binary.PolyProgram Function
abbrev efs := encodeList ef
abbrev edata := encodePair eslots ers
abbrev ed := encodePair edata efs
abbrev eUp := encodePair er efs
abbrev eState : State → List Bool := encodeLoop eUp ed

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianResidualHeight
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
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianListSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Binary.PolyProgram Function

def kernelList (r n : ℕ) (A : RatMatrix r n) : Row :=
  List.ofFn (fun j : Fin n => (kernelVector r n A)[j.val])

def Audit (R N H K r n : ℕ) (A : RatMatrix r n) : Prop :=
  ∀ B∈kernelStates r n A, B.rows ≤ R ∧ B.cols ≤ N ∧
    (∀ i j,HasHeight (values B.data i j) H) ∧
    (∀ j : Fin B.cols,HasHeight ((kernelVector B.rows B.cols B.data)[j.val]) K)

 theorem slots_size (n : ℕ) : (eslots (List.replicate n ())).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,EncodedList.cons_length,eu,List.length_nil,ih]; omega

 theorem audit_head {R N H K r n : ℕ} {A : RatMatrix r n} (h : Audit R N H K r n A) :
    r ≤ R ∧ n ≤ N ∧ (∀ i j,HasHeight (values A i j) H) ∧
    (∀ j : Fin n,HasHeight ((kernelVector r n A)[j.val]) K) := by
  apply h ⟨r,n,A⟩
  cases r with
  | zero => simp only [kernelStates,List.mem_singleton]
  | succ r => cases n <;> simp only [kernelStates,List.mem_cons,true_or]
end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianInputBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Finset Polynomial

abbrev Input.encode (I : Input) := edata I.raw

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianListSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Finset

def returned (r n : ℕ) (A : RatMatrix r n) (fs : Frames) : State :=
  .inr (kernelList r n A,fs)

 theorem down_base (n : ℕ) (A : RatMatrix 0 n) (fs : Frames) :
    body (desc 0 n A fs)=.inr (returned 0 n A fs) := by
  simp only [desc,body,Sum.elim_inl,down,matrix,List.ofFn_zero,List.isEmpty_nil,ite_true]
  rw [basis_ofFn]
  simp only [returned,kernelList,kernelVector,Vector.getElem_ofFn]

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

 theorem audit_pivot {R N H K r n : ℕ} {A : RatMatrix (r+1) (n+1)}
    (ha : Audit R N H K (r+1) (n+1) A)
    (h : (univ.filter (fun j => values A 0 j ≠ 0)).Nonempty) :
    Audit R N H K r n (tabulate (Gaussian.residual (values A) ((univ.filter (fun j => values A 0 j ≠ 0)).min' h))) := by
  intro B hB
  apply ha B
  simp only [kernelStates,dite_eq_left h,List.mem_cons]
  exact Or.inr hB

 theorem audit_skip {R N H K r n : ℕ} {A : RatMatrix (r+1) (n+1)}
    (ha : Audit R N H K (r+1) (n+1) A)
    (h : ¬(univ.filter (fun j => values A 0 j ≠ 0)).Nonempty) :
    Audit R N H K r (n+1) (tabulate (fun i j => values A i.succ j)) := by
  intro B hB
  apply ha B
  simp only [kernelStates,dite_eq_right h,List.mem_cons]
  exact Or.inr hB
end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianBinaryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Binary.PolyProgram Polynomial

def Input.result (I : Input) : Row := kernelList I.rows I.cols I.data

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_IntegerKernelProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Gaussian.IntegerProgram
open Binary Binary.PolyProgram

def Input.result (I : Input) : Row := List.ofFn (computedIntegerKernel I.r I.n I.V)

end MetricKMedian.Gaussian.IntegerProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_AffineListOperations
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

def full (x : Data) (z : Row) : Row :=
  let zs := ((active x).map Prod.fst).zip z
  (List.range x.2.1.length).map (extend zs)

def Input.raw (I : Input) : Data :=
  (List.replicate I.d (),(List.ofFn I.μ.numerator,List.ofFn (fun i => List.ofFn (I.v i))))

theorem entries_raw (I : Input) : entries I.raw=List.ofFn (fun i : Fin I.n =>
    (i.val,(I.μ.numerator i,List.ofFn (I.v i)))) := by
  simp only [entries,Input.raw,Gaussian.ListOperation.zip_ofFn,List.length_ofFn,range_ofFn]

end MetricKMedian.IntegerLaw.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_AffineListCompiler
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
-- module Solutions.OAIQ035_KM.KMedian_Geometry_ComputedRationalCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.RationalLaw
open Finset

theorem scaledFeatures_bound {n d : ℕ} (v : Fin n → Fin d → ℚ) (L : ℕ)
    (hnum : ∀ i j, |(v i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((v i j).den:ℤ) ≤ (2:ℤ)^L) :
    ∀ i j, |scaledFeatures v i j| ≤ (2:ℤ)^(L*(n+1)) := by
  intro i j
  rw [scaledFeatures_eq]
  simpa only [Fintype.card_fin] using RationalScaling.numerator_bound (fun i => v i j) L
    (fun i => hnum i j) (fun i => hden i j) i

end MetricKMedian.RationalLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_PivotListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.IntegerLaw.ListPivot
open Binary Binary.PolyProgram Function Finset
abbrev ee := encodePair Signed.encode Signed.encode

end MetricKMedian.IntegerLaw.ListPivot
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_CompressionListStep
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
-- module Solutions.OAIQ035_KM.KMedian_Rounding_WeightedGridInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section

namespace MetricKMedian.RationalWeightedStep
open Finset RationalGrid
variable {n : ℕ}

theorem endpoint_grid (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (D : ℤ) (hb : ∀ i, At D (β i)) (p : Vector ℚ n)
    (hp : ∀ i, At D (β i*point p i)) (b : Fin 2) :
    ∀ i, At D (β i*point (endpoint β p b) i) := by
  by_cases h : 1 < (fractional p).card
  · let a := pair p h
    let i := a.val.1
    let j := a.val.2
    let r := β i/β j
    let t := if b=0 then up p i j r else -down p i j r
    let q := move p i j r t
    have hij : i≠j := a.property.2.2
    have hr : r≠0 := (div_pos (hβ i) (hβ j)).ne'
    have he : endpoint β p b=q := by rw [endpoint,dite_eq_left h]
    have hw : β i*point q i+β j*point q j=β i*point p i+β j*point p j :=
      move_pair_weighted β p i j hij (hβ j).ne' t
    have hint : (point q i=0 ∨ point q i=1) ∨ (point q j=0 ∨ point q j=1) := by
      by_cases hb0 : b=0
      · have hh := up_integral p i j hij r hr
        simpa only [q,t,hb0,ite_true] using hh.imp (fun hi => Or.inr hi) (fun hj => Or.inl hj)
      · have hh := down_integral p i j hij r hr
        simpa only [q,t,hb0,ite_false] using hh.imp (fun hi => Or.inl hi) (fun hj => Or.inr hj)
    have hpi : At D (β i*point q i) ∧ At D (β j*point q j) := by
      rcases hint with hi | hj
      · have hai : At D (β i*point q i) := by
          rcases hi with hi | hi
          · rw [hi,mul_zero]; exact RationalGrid.zero _
          · rw [hi,mul_one]; exact hb i
        refine ⟨hai,?_⟩
        have hh := RationalGrid.sub (RationalGrid.add (hp i) (hp j)) hai
        convert hh using 1; linarith
      · have haj : At D (β j*point q j) := by
          rcases hj with hj | hj
          · rw [hj,mul_zero]; exact RationalGrid.zero _
          · rw [hj,mul_one]; exact hb j
        refine ⟨?_,haj⟩
        have hh := RationalGrid.sub (RationalGrid.add (hp i) (hp j)) haj
        convert hh using 1; linarith
    intro k
    rw [he]
    by_cases hki : k=i
    · subst k; exact hpi.1
    by_cases hkj : k=j
    · subst k; exact hpi.2
    simpa only [q,point_move_rest _ _ _ _ hki hkj] using hp k
  · simpa only [endpoint,dite_eq_right h] using hp

end MetricKMedian.RationalWeightedStep
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalWeightedInvariants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalWeightedStep
open Finset
variable {n : ℕ}

theorem endpoint_feasible (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (hp : ∀ k, 0 ≤ point p k ∧ point p k ≤ 1) (b : Fin 2) :
    ∀ k, 0 ≤ point (endpoint β p b) k ∧ point (endpoint β p b) k ≤ 1 := by
  by_cases h : 1 < (fractional p).card
  · let a := pair p h
    let r := β a.val.1/β a.val.2
    have hr : 0 < r := div_pos (hβ _) (hβ _)
    have hu := up_pos p _ _ r hr a.property.1 a.property.2.1
    have hd := down_pos p _ _ r hr a.property.1 a.property.2.1
    have hpr0 : ∀ k, 0 ≤ realPoint p k := fun k => by
      dsimp only [realPoint]; exact_mod_cast (hp k).1
    have hpr1 : ∀ k, realPoint p k ≤ 1 := fun k => by
      dsimp only [realPoint]; exact_mod_cast (hp k).2
    have hrr : (0:ℝ) < r := by exact_mod_cast hr
    let t := if b=0 then up p a.val.1 a.val.2 r else -down p a.val.1 a.val.2 r
    have ht0 : -down p a.val.1 a.val.2 r ≤ t := by dsimp only [t]; split_ifs <;> linarith
    have ht1 : t ≤ up p a.val.1 a.val.2 r := by dsimp only [t]; split_ifs <;> linarith
    have ht0r : -WeightedRounding.down (realPoint p) a.val.1 a.val.2 (r:ℝ) ≤ (t:ℝ) := by
      rw [← real_down,← Rat.cast_neg]; exact_mod_cast ht0
    have ht1r : (t:ℝ) ≤ WeightedRounding.up (realPoint p) a.val.1 a.val.2 (r:ℝ) := by
      rw [← real_up]; exact_mod_cast ht1
    have hh := WeightedRounding.move_bounds hpr0 hpr1 a.property.2.2 hrr ht0r ht1r
    rw [← real_move] at hh
    simp only [realPoint] at hh
    intro k
    simp only [endpoint,dite_eq_left h]
    exact ⟨by exact_mod_cast hh.1 k,by exact_mod_cast hh.2 k⟩
  · simpa only [endpoint,dite_eq_right h] using hp

theorem endpoint_smaller (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (h : 1 < (fractional p).card) (b : Fin 2) :
    (fractional (endpoint β p b)).card < (fractional p).card := by
  let a := pair p h
  let r := β a.val.1/β a.val.2
  have hr : (0:ℝ) < r := by exact_mod_cast div_pos (hβ a.val.1) (hβ a.val.2)
  have hi : a.val.1 ∈ MarginalRounding.fractional (realPoint p) := by
    rw [real_fractional]; exact a.property.1
  have hj : a.val.2 ∈ MarginalRounding.fractional (realPoint p) := by
    rw [real_fractional]; exact a.property.2.1
  simp only [endpoint,dite_eq_left h]
  by_cases hb : b=0
  · rw [ite_eq_left hb]
    have hh := WeightedRounding.up_smaller hr a.property.2.2 hi hj
    simpa only [← real_up,← real_move,real_fractional] using hh
  · rw [ite_eq_right hb]
    have hh := WeightedRounding.down_smaller hr a.property.2.2 hi hj
    simpa only [← real_down,← Rat.cast_neg,← real_move,real_fractional] using hh

theorem endpoint_weighted (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (b : Fin 2) :
    (∑ k, β k*point (endpoint β p b) k)=∑ k, β k*point p k := by
  by_cases h : 1 < (fractional p).card
  · let a := pair p h
    let r := β a.val.1/β a.val.2
    let t := if b=0 then up p a.val.1 a.val.2 r else -down p a.val.1 a.val.2 r
    have hb : (β a.val.2:ℝ) ≠ 0 := by exact_mod_cast (hβ a.val.2).ne'
    have hh := WeightedRounding.weighted_sum (fun k => (β k:ℝ)) (realPoint p)
      (i:=a.val.1) (j:=a.val.2) hb (t:ℝ)
    rw [← Rat.cast_div,← real_move] at hh
    simp only [realPoint] at hh
    simp only [endpoint,dite_eq_left h]
    exact_mod_cast hh
  · simp only [endpoint,dite_eq_right h]

end MetricKMedian.RationalWeightedStep
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalSignedStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalSignedStep
open Finset RationalWeightedStep
variable {n : ℕ}

theorem endpoint_weighted (β : Fin n → ℚ) 
    (p : Vector ℚ n) (b : Fin 2) :
    (∑ k, β k*point (endpoint β p b) k)=∑ k, β k*point p k := by
  by_cases h : Active β p
  · let a := pair β p h
    let r := β a.val.1/β a.val.2
    let t := if b=0 then up p a.val.1 a.val.2 r else -down p a.val.1 a.val.2 r
    have hb : (β a.val.2:ℝ) ≠ 0 := by exact_mod_cast pair_right_ne β p h
    have hh := WeightedRounding.weighted_sum (fun k => (β k:ℝ)) (realPoint p)
      (i:=a.val.1) (j:=a.val.2) hb (t:ℝ)
    rw [← Rat.cast_div,← real_move] at hh
    simp only [realPoint] at hh
    simp only [endpoint,dite_eq_left h]
    exact_mod_cast hh
  · simp only [endpoint,dite_eq_right h]

end MetricKMedian.RationalSignedStep
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundingCoordinateHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.RationalGrid
open Binary

theorem table {n : ℕ} (q : Fin n → ℚ) (i : Fin n) : At (RationalScaling.denominator q) (q i) := by
  refine ⟨RationalScaling.numerator q i,?_⟩
  rw [RationalScaling.numerator_cast,mul_div_cancel_right₀ _ (by exact_mod_cast (RationalScaling.denominator_pos q).ne')]

end MetricKMedian.RationalGrid

namespace MetricKMedian.RoundingHeight
open RationalGrid RationalWeightedStep Binary
variable {n : ℕ}

theorem denominator_pos (β : Fin n → ℚ) (p : Vector ℚ n) : 0<denominator β p :=
  mul_pos (RationalScaling.denominator_pos _) (RationalScaling.denominator_pos _)

theorem initial_grid (β : Fin n → ℚ) (p : Vector ℚ n) :
    (∀ i, At (denominator β p) (β i)) ∧ (∀ i, At (denominator β p) (β i*point p i)) :=
  ⟨fun i => enlarge (table β i) _ (RationalScaling.denominator_pos _).ne',
    fun i => RationalGrid.mul (table β i) (table (point p) i)⟩

theorem denominator_bound (β : Fin n → ℚ) (p : Vector ℚ n) (L : ℕ)
    (hb : ∀ i, HasHeight (β i) L) (hp : ∀ i, HasHeight (point p i) L) :
    denominator β p≤(2:ℤ)^(2*n*L) := by
  have h1 := RationalScaling.denominator_bound β L (fun i => (hb i).2)
  have h2 := RationalScaling.denominator_bound (point p) L (fun i => (hp i).2)
  simp only [Fintype.card_fin] at h1 h2
  calc
    _ ≤ (2:ℤ)^(L*n)*(2:ℤ)^(L*n) := mul_le_mul h1 h2 (RationalScaling.denominator_pos _).le (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; ring

theorem coordinate_height (β : Fin n → ℚ) (p q : Vector ℚ n) (L : ℕ)
    (hb : ∀ i, HasHeight (β i) L) (hp : ∀ i, HasHeight (point p i) L)
    (hq : ∀ i, At (denominator β p) (β i*point q i))
    (hz : ∀ i, β i=0 → point q i=point p i)
    (hu : ∀ i, 0≤point q i ∧ point q i≤1) (i : Fin n) :
    HasHeight (point q i) (2*n*L+L) := by
  by_cases hi : β i=0
  · rw [hz i hi]
    exact (hp i).mono (by omega)
  have hD := denominator_pos β p
  have hd := denominator_bound β p L hb hp
  apply RationalGrid.unit_height (mul_ne_zero hD.ne' (by
      intro hz
      apply hi
      rw [← Rat.num_div_den (β i),hz,Int.cast_zero,zero_div]))
    (D := denominator β p * (β i).num)
  · rw [abs_mul,abs_of_pos hD,pow_add]
    exact mul_le_mul hd (hb i).1 (abs_nonneg _) (by positivity)
  · exact divide_weight hD.ne' hi (hq i)
  · rw [abs_of_nonneg (hu i).1]
    exact (hu i).2

end MetricKMedian.RoundingHeight
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundingListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.RoundingList
open Binary Binary.Automatic Binary.Automatic.Poly RationalWeightedStep Finset
abbrev er := encodeList Ratio.encode

theorem second_list {n : ℕ} (p : Vector ℚ n) (h : 1<(RationalWeightedStep.fractional p).card) :
    second p.toList=(RationalWeightedStep.pair p h).val.2.val := by
  unfold second indices
  rw [Vector.length_toList,first_list p h]
  apply findIdx_min
  · rw [← card_pos,card_erase_of_mem (min'_mem _ _)]
    omega
  intro i
  simp only [frac,Vector.getElem?_toList,Vector.getElem?_eq_getElem i.isLt,Option.getD_some,
    ← Bool.decide_and,Finset.mem_erase]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]

  simp only [RationalWeightedStep.pair,Fin.val_ne_iff,RationalWeightedStep.fractional,mem_filter,mem_univ,true_and,point]
  exact and_comm

theorem up_list {n : ℕ} (p : Vector ℚ n) (i j : Fin n) (r : ℚ) :
    up p.toList i.val j.val r=RationalWeightedStep.up p i j r := by simp only [up,RationalWeightedStep.up,get_point]
theorem down_list {n : ℕ} (p : Vector ℚ n) (i j : Fin n) (r : ℚ) :
    down p.toList i.val j.val r=RationalWeightedStep.down p i j r := by simp only [down,RationalWeightedStep.down,get_point]
theorem move_list {n : ℕ} (p : Vector ℚ n) (i j : Fin n) (r t : ℚ) :
    move p.toList i.val j.val r t=(RationalWeightedStep.move p i j r t).toList := by
  simp only [move,indices,Vector.length_toList,range_finRange,List.map_map,RationalWeightedStep.move,Vector.toList_ofFn,List.ofFn_eq_map]
  congr 1
  funext k
  simp only [Function.comp_def,get_point,Fin.val_inj]

theorem probability_list {n : ℕ} (β : Fin n → ℚ) (p : Vector ℚ n) :
    probability (List.ofFn β) p.toList=RationalWeightedStep.probability β p := by
  unfold probability RationalWeightedStep.probability
  rw [active_list]
  simp only [decide_eq_true_eq]
  split_ifs with h
  · simp only [ratio,first_list p h,second_list p h,Gaussian.ListOperation.get_ofFn,up_list,down_list]
  · rfl

theorem endpoint_list {n : ℕ} (β : Fin n → ℚ) (p : Vector ℚ n) (b : Fin 2) :
    endpoint (List.ofFn β) p.toList (decide (b≠0))=(RationalWeightedStep.endpoint β p b).toList := by
  unfold endpoint RationalWeightedStep.endpoint
  rw [active_list]
  simp only [decide_eq_true_eq]
  by_cases h : 1<(RationalWeightedStep.fractional p).card
  · simp only [ite_eq_left h,dite_eq_left h,ratio,first_list p h,second_list p h,Gaussian.ListOperation.get_ofFn,up_list,down_list]
    by_cases hb : b=0 <;> simp [hb,move_list]
  · simp only [ite_eq_right h,dite_eq_right h]

end MetricKMedian.RoundingList
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_RationalFeatureProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function
abbrev eqr := encodeList Ratio.encode
abbrev eqm := encodeList eqr
abbrev QData := List Unit × (LawData × QRows)

structure RationalInput where
  n : ℕ
  d : ℕ
  μ : IntegerLaw (Fin n)
  v : Fin n → Fin d → ℚ

def RationalInput.lawData (I : RationalInput) : LawData := (I.μ.denominator,List.ofFn I.μ.numerator)
def RationalInput.features (I : RationalInput) : QRows := List.ofFn (fun i => List.ofFn (I.v i))
def RationalInput.raw (I : RationalInput) : QData := (List.replicate I.d (),(I.lawData,I.features))

def RationalInput.integer (I : RationalInput) : Input := ⟨I.n,I.d,I.μ,RationalLaw.scaledFeatures I.v⟩

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundingUniformStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse
abbrev erow := RoundingList.er

theorem encodeList_map {α β : Type} (eb : β → List Bool) (f : α → β) (xs : List α) :
    encodeList eb (xs.map f)=encodeList (fun x => eb (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, encodeList,ih]

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseIterationHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section

namespace MetricKMedian.RationalWeightedStep
open Binary
variable {n : ℕ}

theorem up_height (p : Vector ℚ n) (i j : Fin n) (r : ℚ) (A B : ℕ)
    (hp : ∀ i, HasHeight (point p i) A) (hr : HasHeight r B) :
    HasHeight (up p i j r) (A+B+1) := by
  exact ((HasHeight.one 0 |>.sub (hp i)).mono (by omega)).min ((hp j |>.div hr).mono (by omega))
theorem down_height (p : Vector ℚ n) (i j : Fin n) (r : ℚ) (A B : ℕ)
    (hp : ∀ i, HasHeight (point p i) A) (hr : HasHeight r B) :
    HasHeight (down p i j r) (A+B+1) := by
  exact ((hp i).mono (by omega)).min (((HasHeight.one 0 |>.sub (hp j)).div hr).mono (by omega))
theorem probability_height (β : Fin n → ℚ) (p : Vector ℚ n) (A B : ℕ)
    (hβ : ∀ i, HasHeight (β i) B) (hp : ∀ i, HasHeight (point p i) A) :
    HasHeight (probability β p) (3*(A+2*B+1)+1) := by
  unfold probability
  split_ifs with h
  · let a := pair p h
    have hr := (hβ a.val.1).div (hβ a.val.2)
    have hu := up_height p a.val.1 a.val.2 _ A (B+B) hp hr
    have hd := down_height p a.val.1 a.val.2 _ A (B+B) hp hr
    convert hd.div (hu.add hd) using 1 <;> first | rfl | ring
  · exact HasHeight.zero _
end MetricKMedian.RationalWeightedStep

namespace MetricKMedian.RationalSignedStep
open Binary RationalWeightedStep
variable {n : ℕ}
theorem probability_height (β : Fin n → ℚ) (p : Vector ℚ n) (A B : ℕ)
    (hβ : ∀ i, HasHeight (β i) B) (hp : ∀ i, HasHeight (point p i) A) :
    HasHeight (probability β p) (3*(A+2*B+1)+1) := by
  unfold probability
  split_ifs with h
  · let a := pair β p h
    have hr := (hβ a.val.1).div (hβ a.val.2)
    have hu := up_height p a.val.1 a.val.2 _ A (B+B) hp hr
    have hd := down_height p a.val.1 a.val.2 _ A (B+B) hp hr
    convert hd.div (hu.add hd) using 1 <;> first | rfl | ring
  · exact HasHeight.zero _
end MetricKMedian.RationalSignedStep

end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_GraphLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseGraph.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
abbrev qr := encodeList Ratio.encode
abbrev qt := encodeList qr
abbrev eqi := encodePair (encodeList (fun _ : Unit => [])) qt

abbrev QInput.encode (x : QInput) := eqi x.raw

end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalCopyTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch
variable {F : Type} [DecidableEq F] [Fintype F] {Δ : ℕ}

def sources {I : Type} [DecidableEq I] [Fintype I]
    (G : I → Finset I) (H : Finset I) (Z : Finset (HeavyAction (graph G) H)) : Finset I :=
  H ∪ (Z ∩ (heavy (graph G) H).ordinary).image (heavy (graph G) H).source

def opened (A : Finset (CopyState.Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graph G) H)) : Finset F :=
  (sources G H Z).image (fun i => i.val.1)

end MetricKMedian.RationalBatchData
end
end

end OAI
end


