-- Prove2me | Definitions.Def_OAIQ035K007
-- name    : OAIQ035K007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:53:35.198325+00:00
-- url     : https://prove2.me/theorems/9a8bba4e-9b1d-45c3-a916-dba6725db285
-- title:
--   Definitions bundle OAIQ035K007 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 97 declarations of OpenAI's Lean: 67 definitions, 3 inductive types or structures and 27 theorems. The definitions and types are `OAI.MetricKMedian.FractionalDual.affine`, `OAI.MetricKMedian.Gaussian.IntegerProgram.Input`, `OAI.MetricKMedian.Gaussian.ListOperation.Desc`, `OAI.MetricKMedian.Gaussian.ListOperation.Frame`, `OAI.MetricKMedian.Gaussian.ListOperation.Frames`, `OAI.MetricKMedian.Gaussian.ListOperation.Row`, `OAI.MetricKMedian.Gaussian.ListOperation.Rows`, `OAI.MetricKMedian.Gaussian.ListOperation.State`, `OAI.MetricKMedian.Gaussian.ListOperation.Up`, `OAI.MetricKMedian.Gaussian.ListOperation.basis`, `OAI.MetricKMedian.Gaussian.ListOperation.body`, `OAI.MetricKMedian.Gaussian.ListOperation.coefficients`, `OAI.MetricKMedian.Gaussian.ListOperation.down`, `OAI.MetricKMedian.Gaussian.ListOperation.erase`, `OAI.MetricKMedian.Gaussian.ListOperation.eu`, `OAI.MetricKMedian.Gaussian.ListOperation.frameBound`, `OAI.MetricKMedian.Gaussian.ListOperation.framesBound`, `OAI.MetricKMedian.Gaussian.ListOperation.insert`, `OAI.MetricKMedian.Gaussian.ListOperation.lift`, `OAI.MetricKMedian.Gaussian.ListOperation.matrix`, `OAI.MetricKMedian.Gaussian.ListOperation.matrixBound`, `OAI.MetricKMedian.Gaussian.ListOperation.pivot`, `OAI.MetricKMedian.Gaussian.ListOperation.reduce`, `OAI.MetricKMedian.Gaussian.ListOperation.residual`, `OAI.MetricKMedian.Gaussian.ListOperation.residualPolynomial`, `OAI.MetricKMedian.Gaussian.ListOperation.returnPolynomial`, `OAI.MetricKMedian.Gaussian.ListOperation.rowBound`, `OAI.MetricKMedian.Gaussian.ListOperation.stateBound`, `OAI.MetricKMedian.Gaussian.ListOperation.statePolynomial`, `OAI.MetricKMedian.Gaussian.ListOperation.up`, `OAI.MetricKMedian.Gaussian.ResidualCertificate`, `OAI.MetricKMedian.Gaussian.ResidualCertificate.skip`, `OAI.MetricKMedian.Gaussian.residualHeight`, `OAI.MetricKMedian.Gaussian.returnHeight`, `OAI.MetricKMedian.Gaussian.rowValue`, `OAI.MetricKMedian.InstanceProgram.Matrix`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.QRow`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.QRows`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.height`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.heightPolynomial` and 30 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Compression_AffineListOperations`, `KMedian_Compression_CompressionBounds`, `KMedian_Compression_GaussianInputBounds`, `KMedian_Compression_GaussianListCompiler`, `KMedian_Compression_GaussianListMachine`, `KMedian_Compression_GaussianListOperations`, `KMedian_Compression_GaussianListPivot`, `KMedian_Compression_GaussianListSize`, `KMedian_Compression_GaussianResidualCertificate`, `KMedian_Compression_GaussianResidualHeight`, `KMedian_Compression_GaussianStates`, `KMedian_Compression_IntegerKernelProgram`, `KMedian_Compression_RationalKernelHeightSupport`, `KMedian_Geometry_GraphRunHeight`, `KMedian_Geometry_ListSigma`, `KMedian_Optimization_FractionalDual`, `KMedian_Probability_BernoulliRunHeight`, `KMedian_Probability_BernoulliRunProgram`, `KMedian_Process_BatchOrdinalCodes`, `KMedian_Process_PhysicalBatchProgram`, `KMedian_Process_PhysicalPotential`, `KMedian_Process_RoundingListOperations`, `KMedian_Process_RoundingRunHeight`, `KMedian_Process_RoundingRunProgram`, `KMedian_Programs_GraphRunProgram`, `KMedian_Programs_InstanceDataProgram`, `KMedian_Programs_RationalFeatureProgram`, `KMedian_Rounding_SignedListOperations`, `KMedian_Rounding_SignedPreparationProgram`, `KMedian_Sparse_SparseBranchProgram`, `KMedian_Sparse_SparseIterationHeight`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K020`, `OAIQ035K021`, `OAIQ035K024` and `OAIQ035K062`; the statement `OAI_MetricKMedian_CopyState_valid_advance`; the proof of `OAI_MetricKMedian_CopyState_valid_advance`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianListOperations
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

abbrev Row := List ℚ
abbrev Rows := List Row

def erase (as : List α) (p : ℕ) := as.take p++(as.drop p).tail

def insert (as : List α) (p : ℕ) (a : α) := as.take p++a::as.drop p

def pivot (row : Row) : ℕ := row.findIdx (fun q => decide (q≠0))

def coefficients (row : Row) (p : ℕ) : Row := (erase row p).map (fun q => q/row[p]?.getD 0)

def reduce (c : Row) (p : ℕ) (row : Row) : Row :=
  ((erase row p).zip c).map (fun x => x.1-x.2*row[p]?.getD 0)

def residual (row : Row) (p : ℕ) (rows : Rows) : Rows :=
  rows.map (reduce (coefficients row p) p)

def lift (row : Row) (p : ℕ) (z : Row) : Row :=
  insert z p (-(((coefficients row p).zip z).map (fun x => x.1*x.2)).sum)

def basis (slots : List Unit) : Row :=
  if slots.isEmpty then [] else 1::slots.tail.map (fun _ => 0)

def matrix {r n : ℕ} (A : Fin r → Fin n → ℚ) : Rows :=
  List.ofFn (fun i => List.ofFn (A i))

 theorem erase_eq (as : List α) (p : ℕ) : erase as p=as.eraseIdx p := by
  simp only [erase,List.eraseIdx_eq_take_drop_succ,List.tail_drop]

 theorem insert_eq (as : List α) (p : ℕ) (a : α) (h : p≤as.length) :
    insert as p a=as.insertIdx p a := by
  induction as generalizing p with
  | nil =>
      have hp : p=0 := by simpa using h
      subst p
      rfl
  | cons b bs ih =>
      cases p with
      | zero => rfl
      | succ p =>
          simp only [insert,List.take_succ_cons,List.drop_succ_cons,List.cons_append,List.insertIdx_succ_cons]
          congr 1
          exact ih p (by simpa only [List.length_cons,Nat.succ_le_succ_iff] using h)

 theorem basis_ofFn (n : ℕ) : basis (List.replicate n ())=List.ofFn (fun j : Fin n => if j.val=0 then (1:ℚ) else 0) := by
  cases n with
  | zero => simp [basis]
  | succ n =>
      rw [List.ofFn_succ]
      simp only [basis,List.replicate_succ,List.isEmpty_cons,Bool.false_eq_true,ite_false,List.tail_cons,List.map_replicate,Fin.val_zero,ite_true]
      congr 1
      simp only [Fin.val_succ,Nat.succ_ne_zero,ite_false,List.ofFn_const]
end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianListCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Gaussian.ListOperation
open Function
abbrev eu : Unit → List Bool := fun _ => []
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
open Function
abbrev Frame := ℕ × Row
abbrev Frames := List Frame
abbrev Desc := (List Unit × Rows) × Frames
abbrev Up := Row × Frames
abbrev State := Desc ⊕ Up

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
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianResidualCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                   
section
namespace MetricKMedian.Gaussian
open Finset

def rowValue {R N : ℕ} (A : Fin R → Fin N → ℚ) (v : Fin R → ℚ) (j : Fin N) : ℚ :=
  ∑ i, A i j*v i

 theorem rowValue_sub {R N : ℕ} (A : Fin R → Fin N → ℚ) (u v : Fin R → ℚ)
    (t : ℚ) (j : Fin N) :
    rowValue A (fun i => u i-t*v i) j=rowValue A u j-t*rowValue A v j := by
  simp only [rowValue,mul_sub,sum_sub_distrib]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  ring

 theorem rowValue_smul {R N : ℕ} (A : Fin R → Fin N → ℚ) (v : Fin R → ℚ)
    (t : ℚ) (j : Fin N) : rowValue A (fun i => t*v i) j=t*rowValue A v j := by
  simp only [rowValue,mul_sum]
  apply sum_congr rfl
  intro i _
  ring

structure ResidualCertificate {R N r n : ℕ} (A : Fin R → Fin N → ℚ)
    (B : Fin r → Fin n → ℚ) where
  pivotRows : Finset (Fin R)
  pivotCols : Finset (Fin N)
  row : Fin r → Fin R
  col : Fin n → Fin N
  row_injective : Function.Injective row
  col_injective : Function.Injective col
  row_outside : ∀ i, row i ∉ pivotRows
  coefficient : Fin r → Fin R → ℚ
  normalized : ∀ i, coefficient i (row i)=1
  supported : ∀ i j, j ∉ pivotRows → j ≠ row i → coefficient i j=0
  annihilates : ∀ i j, j ∈ pivotCols → rowValue A (coefficient i) j=0
  represents : ∀ i j, B i j=rowValue A (coefficient i) (col j)
  independent : ∀ v : Fin R → ℚ, (∀ i, i ∉ pivotRows → v i=0) →
    (∀ j, j ∈ pivotCols → rowValue A v j=0) → ∀ i, v i=0

namespace ResidualCertificate
variable {R N r n : ℕ} {A : Fin R → Fin N → ℚ} {B : Fin r → Fin n → ℚ}

 theorem decompose (P : ResidualCertificate A B) (i : Fin r) (v : Fin R → ℚ)
    (hv : ∀ j, j ∉ P.pivotRows → j ≠ P.row i → v j=0)
    (hk : ∀ j, j ∈ P.pivotCols → rowValue A v j=0) :
    ∀ j, v j=v (P.row i)*P.coefficient i j := by
  have hzero := P.independent (fun j => v j-v (P.row i)*P.coefficient i j) (by
    intro j hj
    by_cases he : j=P.row i
    · subst j; rw [P.normalized,mul_one,sub_self]
    · rw [hv j hj he,P.supported i j hj he,mul_zero,sub_self]) (by
    intro j hj
    rw [rowValue_sub,hk j hj,P.annihilates i j hj,mul_zero,sub_self])
  intro j
  exact sub_eq_zero.mp (hzero j)

 def skip {B : Fin (r+1) → Fin n → ℚ} (P : ResidualCertificate A B) :
    ResidualCertificate A (fun i j => B i.succ j) where
  pivotRows := P.pivotRows
  pivotCols := P.pivotCols
  row i := P.row i.succ
  col := P.col
  col_injective := P.col_injective
  row_injective := P.row_injective.comp (Fin.succ_injective _)
  row_outside i := P.row_outside i.succ
  coefficient i := P.coefficient i.succ
  normalized i := P.normalized i.succ
  supported i := P.supported i.succ
  annihilates i := P.annihilates i.succ
  represents i := P.represents i.succ
  independent := P.independent

variable {B' : Fin (r+1) → Fin (n+1) → ℚ}

 theorem next_row_ne (P : ResidualCertificate A B') (i : Fin r) : P.row i.succ ≠ P.row 0 := by
  intro he
  exact Fin.succ_ne_zero i (P.row_injective he)

 theorem firstCoeff_next (P : ResidualCertificate A B') (i : Fin r) :
    P.coefficient 0 (P.row i.succ)=0 :=
  P.supported 0 _ (P.row_outside _) (P.next_row_ne i)

end ResidualCertificate
end MetricKMedian.Gaussian
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_RationalKernelHeightSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                   
section
namespace MetricKMedian.Gaussian
open Finset

theorem row_scaling_kernel_iff {r n : ℕ} (A : Fin r → Fin n → ℚ)
    (s : Fin r → ℚ) (hs : ∀ i, s i ≠ 0) (z : Fin n → ℚ) :
    (∀ i, ∑ j, (A i j*s i)*z j=0) ↔ (∀ i, ∑ j, A i j*z j=0) := by
  have he : ∀ i, (∑ j, (A i j*s i)*z j)=(∑ j, A i j*z j)*s i := by
    intro i
    rw [sum_mul]
    apply sum_congr rfl
    intro j _
    ring
  simp only [he,mul_eq_zero,hs,or_false]

end MetricKMedian.Gaussian
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

def residualHeight (R N L : ℕ) : ℕ := R+2*N*(N+L*(R+1))+L*(R+1)

end MetricKMedian.Gaussian
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianStates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Gaussian
open Finset

def returnHeight (R N L : ℕ) : ℕ := 2*R*(R+residualHeight R N L*(N+1))

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
open Function

def rowBound (N H : ℕ) := N*(2*(3*H+10)+1)
def matrixBound (R N H : ℕ) := R*(2*rowBound N H+1)
def frameBound (N H : ℕ) := 2*(N+1)+1+rowBound N H
def framesBound (R N H : ℕ) := R*(2*frameBound N H+1)
def stateBound (R N H K : ℕ) := 4*N+2*matrixBound R N H+2*rowBound N K+2*framesBound R N H+10

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
open Finset Polynomial

 theorem residualHeight_mono {r n l R N L : ℕ} (hr : r ≤ R) (hn : n ≤ N) (hl : l ≤ L) :
    residualHeight r n l ≤ residualHeight R N L := by
  unfold residualHeight
  gcongr

 theorem returnHeight_mono {r n l R N L : ℕ} (hr : r ≤ R) (hn : n ≤ N) (hl : l ≤ L) :
    returnHeight r n l ≤ returnHeight R N L := by
  have hh := residualHeight_mono hr hn hl
  unfold returnHeight
  gcongr

noncomputable def residualPolynomial : Polynomial ℕ := X+2*X*(X+X*(X+1))+X*(X+1)
noncomputable def returnPolynomial : Polynomial ℕ := 2*X*(X+residualPolynomial*(X+1))
noncomputable def statePolynomial : Polynomial ℕ :=
  let rowH := X*(2*(3*residualPolynomial+10)+1)
  let rowK := X*(2*(3*returnPolynomial+10)+1)
  let mat := X*(2*rowH+1)
  let frame := 2*(X+1)+1+rowH
  let frames := X*(2*frame+1)
  4*X+2*mat+2*rowK+2*frames+10

 theorem residualPolynomial_eval (L : ℕ) : residualPolynomial.eval L=residualHeight L L L := by
  simp only [residualPolynomial,residualHeight,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
 theorem returnPolynomial_eval (L : ℕ) : returnPolynomial.eval L=returnHeight L L L := by
  simp only [returnPolynomial,returnHeight,eval_add,eval_mul,eval_X,eval_ofNat,eval_one,residualPolynomial_eval]
 theorem statePolynomial_eval (L : ℕ) : statePolynomial.eval L=
    stateBound L L (residualHeight L L L) (returnHeight L L L) := by
  simp only [statePolynomial,stateBound,rowBound,matrixBound,frameBound,framesBound,eval_add,eval_mul,eval_X,eval_ofNat,eval_one,residualPolynomial_eval,returnPolynomial_eval]
end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianListPivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.Gaussian.ListOperation
open Finset
 theorem pivot_ofFn {n : ℕ} (f : Fin n → ℚ)
    (h : (univ.filter (fun j => f j≠0)).Nonempty) :
    pivot (List.ofFn f)=(univ.filter (fun j => f j≠0)).min' h := by
  let p := (univ.filter (fun j => f j≠0)).min' h
  change (List.ofFn f).findIdx (fun q => decide (q≠0))=p.val
  apply (List.findIdx_eq (by simpa only [List.length_ofFn] using p.isLt)).mpr
  constructor
  · simpa only [List.getElem_ofFn,decide_eq_true_eq] using (mem_filter.mp (min'_mem _ h)).2
  · intro j hj
    simp only [List.getElem_ofFn,decide_eq_false_iff_not,not_not]
    by_contra hz
    have hm : p ≤ (⟨j,Nat.lt_trans hj p.isLt⟩ : Fin n) := min'_le (univ.filter (fun j => f j≠0)) (⟨j,Nat.lt_trans hj p.isLt⟩ : Fin n) (mem_filter.mpr ⟨mem_univ _,hz⟩)
    exact (not_le_of_gt hj) hm
 theorem pivot_ofFn_zero {n : ℕ} (f : Fin n → ℚ)
    (h : ¬(univ.filter (fun j => f j≠0)).Nonempty) :
    pivot (List.ofFn f)=n := by
  change (List.ofFn f).findIdx (fun q => decide (q≠0))=n
  apply Eq.trans (b:=(List.ofFn f).length) ?_ List.length_ofFn
  apply List.findIdx_eq_length_of_false
  intro a ha
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
  simp only [decide_eq_false_iff_not,not_not]
  by_contra hz
  exact h ⟨j,mem_filter.mpr ⟨mem_univ _,hz⟩⟩
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

structure Input where
  r : ℕ
  n : ℕ
  V : Fin r → Fin n → ℤ
  underdetermined : r < n

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
open Gaussian
open Finset

def extend (zs : List (ℕ × ℤ)) (i : ℕ) : ℤ :=
  ((zs.filter (fun e => decide (e.1=i))).map Prod.snd).sum

theorem indices_ofFn (n : ℕ) : List.range n=List.ofFn (fun i : Fin n => i.val) := by
  apply List.ext_getElem
  · simp
  · intros; simp

end MetricKMedian.IntegerLaw.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_FractionalDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FractionalDual
open Finset
variable {ι : Type} [Fintype ι]

def affine (d y : ι → ℚ) (τ : ℚ) : ℚ := τ-∑ i, y i*max 0 (τ-d i)

end MetricKMedian.FractionalDual
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_CompressionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Function Finset Polynomial

def height (L : ℕ) := L+(2*(L+1)*(L+1+L)*(L+1))*L
noncomputable def heightPolynomial : Polynomial ℕ := X+(2*(X+1)*(X+1+X)*(X+1))*X
noncomputable def statePolynomial : Polynomial ℕ := 3*X+2+2*(X+1)*(2*heightPolynomial+9)

theorem heightPolynomial_eval (L : ℕ) : heightPolynomial.eval L=height L := by
  simp only [heightPolynomial,height,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]

theorem statePolynomial_eval (L : ℕ) :
    statePolynomial.eval L=3*L+2+2*(L+1)*(2*height L+9) := by
  simp only [statePolynomial,eval_add,eval_mul,eval_ofNat,eval_X,eval_one,heightPolynomial_eval]

theorem size_arithmetic (L d den num feat H : ℕ) (hd : d≤L) (hden : den≤H+4)
    (hnum : num≤L*(2*(H+4)+1)) (hfeat : feat≤L) :
    2*d+1+(2*(2*den+1+num)+1+feat)≤3*L+2+2*(L+1)*(2*H+9) := by
  nlinarith

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_GraphRunHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseGraph
variable {n m : ℕ}

def stepHeight (n m N L : ℕ) :=
  let d := n*m+(n*m)*(n*m)
  L+((2*(d+1)*(d+1))*((d+1)*N+1))*((d+1)*N)

end MetricKMedian.SparseGraph
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_ListSigma
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                 
section
namespace MetricKMedian.ListSigma
open Finset

 theorem take_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (k : ℕ) (hk : k ≤ n) :
    (List.ofFn f).take k=List.ofFn (fun i : Fin k => f (Fin.castLE hk i)) := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_ofFn,Nat.min_eq_left hk]
  · intro i hi hi'
    simp only [List.getElem_take,List.getElem_ofFn]
    rfl

 theorem flatten_entry {α : Type} (xs : List (List α)) (i : ℕ) (hi : i<xs.length)
    (j : ℕ) (hj : j<xs[i].length) :
    xs.flatten[((xs.take i).map List.length).sum+j]?=some (xs[i][j]) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero =>
      simp only [List.take_zero,List.map_nil,List.sum_nil,zero_add,List.flatten_cons,List.getElem_cons_zero] at *
      have hj' : j<a.length := hj
      rw [List.getElem?_append_left hj',List.getElem?_eq_getElem hj']
    | succ i =>
      have hi' : i<xs.length := by simpa using hi
      simp only [List.take_succ_cons,List.map_cons,List.sum_cons,List.flatten_cons,List.getElem_cons_succ] at *
      rw [Nat.add_assoc,List.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      exact ih i hi' hj

 theorem ofFn_sigma {α : Type} {m : ℕ} {n : Fin m → ℕ} (f : (i : Fin m) → Fin (n i) → α) :
    (List.ofFn (fun i => List.ofFn (f i))).flatten=
      List.ofFn (fun j => let z := (finSigmaFinEquiv (n:=n)).symm j; f z.1 z.2) := by
  have hlen : (List.ofFn (fun i => List.ofFn (f i))).flatten.length=∑i,n i := by
    simp only [List.length_flatten,List.map_ofFn,List.length_ofFn,Function.comp_def,List.sum_ofFn]
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using hlen
  · intro k hk hk'
    let j : Fin (∑i,n i) := ⟨k,by simpa only [List.length_ofFn] using hk'⟩
    let z := (finSigmaFinEquiv (n:=n)).symm j
    have hindex : (∑i : Fin z.1.val,n (Fin.castLE z.1.isLt.le i))+z.2.val=k := by
      rw [← finSigmaFinEquiv_apply z]
      exact congrArg Fin.val (Equiv.apply_symm_apply _ j)
    have he := flatten_entry (List.ofFn (fun i => List.ofFn (f i))) z.1.val
      (by simpa only [List.length_ofFn] using z.1.isLt) z.2.val
      (by simpa only [List.getElem_ofFn,List.length_ofFn] using z.2.isLt)
    rw [take_ofFn _ _ z.1.isLt.le] at he
    simp only [List.map_ofFn,Function.comp_def,List.length_ofFn,List.sum_ofFn,List.getElem_ofFn] at he
    rw [hindex,List.getElem?_eq_getElem hk] at he
    simpa only [List.getElem_ofFn] using Option.some.inj he

end MetricKMedian.ListSigma
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

namespace MetricKMedian.SparseIntegerLaw
variable {α : Type} {d : ℕ}

def stepHeight (N d P F : ℕ) := P*N+(((2*(d+1)*(d+1+F*(2*N+1)))*(2*N+1))*(2*N))

end MetricKMedian.SparseIntegerLaw
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliRunHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.SparseBernoulli
variable {n d : ℕ}

def stepHeight (n d L : ℕ) := SparseIntegerLaw.stepHeight ((n+1)^d+1) ((n+1)^d) L 0

end MetricKMedian.SparseBernoulli
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
open Finset

theorem findIdx_min {n : ℕ} (s : Finset (Fin n)) (hs : s.Nonempty) (f : ℕ → Bool)
    (hf : ∀ i : Fin n, f i.val=decide (i∈s)) :
    (List.range n).findIdx f=(s.min' hs).val := by
  let i := s.min' hs
  apply (List.findIdx_eq (by simpa only [List.length_range] using i.isLt)).mpr
  constructor
  · simp only [List.getElem_range]
    rw [hf i,decide_eq_true_eq]
    exact min'_mem s hs
  · intro j hj
    simp only [List.getElem_range]
    rw [hf ⟨j,Nat.lt_trans hj i.isLt⟩,decide_eq_false_iff_not]
    intro hm
    exact (not_le_of_gt hj) (s.min'_le _ hm)

end MetricKMedian.RoundingList
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_SignedListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.RoundingList
open Finset

theorem ofFn_product {m n : ℕ} {α : Type} (f : Fin m → Fin n → α) :
    (List.ofFn (fun i => (List.ofFn (f i)))).flatten=
      List.ofFn (fun z : Fin (m*n) => f (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2) := by
  rw [List.ofFn_mul]
  congr 1
  congr 1
  funext i
  have bound (j : Fin n) : i.val*n+j.val < m*n := by
    have hh := Nat.mul_le_mul_right n (Nat.succ_le_iff.mpr i.isLt)
    simp only [Nat.succ_mul] at hh
    omega
  have he (j : Fin n) : (finProdFinEquiv.symm ⟨i.val*n+j.val,bound j⟩ : Fin m × Fin n)=(i,j) := by
    have hh : (⟨i.val*n+j.val,bound j⟩ : Fin (m*n))=finProdFinEquiv (i,j) := by
      apply Fin.ext
      change i.val*n+j.val=j.val+n*i.val
      ring
    rw [hh]
    exact finProdFinEquiv.symm_apply_apply (i,j)
  exact congrArg List.ofFn (funext (he · |> congrArg (fun z => f z.1 z.2))) |>.symm

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
open Function
abbrev QRow := List ℚ
abbrev QRows := List QRow
end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBranchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Function
variable {α γ : Type}

theorem two_expand {n : ℕ} {δ : Type} (f : Fin n → Fin 2 → δ) :
    List.ofFn (fun i : Fin (n*2) => f (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)=
      (List.ofFn (fun i => [f i 0,f i 1])).flatten := by
  rw [List.ofFn_mul]
  congr 1
  congr 1
  funext i
  have he (j : Fin 2) : (finProdFinEquiv.symm ⟨i.val*2+j.val,by omega⟩ : Fin n × Fin 2)=(i,j) :=
    by
      have hh : (⟨i.val*2+j.val,by omega⟩ : Fin (n*2))=finProdFinEquiv (i,j) := by
        apply Fin.ext
        change i.val*2+j.val=j.val+2*i.val
        omega
      rw [hh]
      exact finProdFinEquiv.symm_apply_apply (i,j)
  simp only [he]
  simp [List.ofFn_succ]

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliRunProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseBernoulli.Program
open Function Polynomial

def supportBound (d L : ℕ) := (L+1)^d+1
def heightBound (d L : ℕ) := SparseBernoulli.stepHeight L d L*L
def sizeBound (d L : ℕ) :=
  2*(3*L+2)+1+(2*(2*(heightBound d L+4)+1+supportBound d L*(2*(heightBound d L+4)+1))+1+
    supportBound d L*(2*(3*L)+1))
noncomputable def SPoly (d : ℕ) : Polynomial ℕ := (X+1)^d+1
noncomputable def HPoly (d : ℕ) : Polynomial ℕ :=
  (X*SPoly d+(2*((X+1)^d+1)*((X+1)^d+1+0*(2*SPoly d+1)))*(2*SPoly d+1)*(2*SPoly d))*X
noncomputable def sizePolynomial (d : ℕ) : Polynomial ℕ :=
  2*(3*X+2)+1+(2*(2*(HPoly d+4)+1+SPoly d*(2*(HPoly d+4)+1))+1+SPoly d*(2*(3*X)+1))

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential

noncomputable def cost {I : Type*} (g : ℝ) (d : I → ℝ) (S : Finset I) : ℝ :=
  ∑ i ∈ S, g * d i

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_BatchOrdinalCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.RationalBatchData.Ordinal
open Finset
variable {I : Type} [LinearOrder I] {n : ℕ}
variable (r : Fin n ≃o I)
  (H : Finset I)

abbrev pairOrder : LinearOrder (I × I) :=
  LinearOrder.lift' (fun p : I × I => toLex p) (fun _ _ h => h)
end MetricKMedian.RationalBatchData.Ordinal
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalBatchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparsePhysicalBatch.Program
open Function
open SparseIntegerLaw.BinarySparse

structure Input where
  n : ℕ
  Z : Finset (Fin n)
  C : Fin n → Finset (Fin n)
  p : ℚ
  q : Fin n → ℚ
  hp : 0≤p ∧ p≤1
  hq : ∀ e, 0≤q e ∧ q e≤1

end MetricKMedian.SparsePhysicalBatch.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundingRunHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.RoundingHeight
variable {n : ℕ}

def stepHeight (n L : ℕ) := SparseIntegerLaw.stepHeight (n+n*n+1) (n+n*n)
  (3*(2*n*L+L+2*L+1)+1) (2*(2*n*L+L))

end MetricKMedian.RoundingHeight
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundingRunProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.RoundingProgram
open Function Polynomial
open SparseIntegerLaw.BinarySparse

def heightBound (L : ℕ) := RoundingHeight.stepHeight L L*L
def supportBound (L : ℕ) := L+L*L+1

noncomputable def CPoly : Polynomial ℕ := 2*X*X+X
noncomputable def NPoly : Polynomial ℕ := X+X*X+1
noncomputable def HPoly : Polynomial ℕ :=
  ((3*(CPoly+2*X+1)+1)*NPoly+
    (2*(X+X*X+1)*(X+X*X+1+(2*CPoly)*(2*NPoly+1)))*(2*NPoly+1)*(2*NPoly))*X
noncomputable def statePolynomial : Polynomial ℕ :=
  2*X+1+(2*(2*(HPoly+4)+1+NPoly*(2*(HPoly+4)+1))+1+NPoly*(2*(X*(2*(3*CPoly+10)+1))+1))

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_GraphRunProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseGraph.Program
open Function Polynomial
open SparseIntegerLaw.BinarySparse

def supportBound (L : ℕ) := L*L+(L*L)*(L*L)+1
def heightBound (L : ℕ) := SparseGraph.stepHeight L L L L*L
def graphSize (L : ℕ) := L*(2*(3*L)+1)
def sizeBound (L : ℕ) :=
  2*(3*L+2)+1+(2*(2*(heightBound L+4)+1+supportBound L*(2*(heightBound L+4)+1))+1+
    supportBound L*(2*graphSize L+1))
noncomputable def SPoly : Polynomial ℕ := X*X+(X*X)*(X*X)+1
noncomputable def HPoly : Polynomial ℕ := (X+(2*SPoly*SPoly)*(SPoly*X+1)*(SPoly*X))*X
noncomputable def APoly : Polynomial ℕ := X*(2*(3*X)+1)
noncomputable def sizePolynomial : Polynomial ℕ :=
  2*(3*X+2)+1+(2*(2*(HPoly+4)+1+SPoly*(2*(HPoly+4)+1))+1+SPoly*(2*APoly+1))
theorem sizePolynomial_eval (L : ℕ) : sizePolynomial.eval L=sizeBound L := by
  simp only [sizePolynomial,sizeBound,heightBound,supportBound,graphSize,HPoly,SPoly,APoly,
    SparseGraph.stepHeight,eval_add,eval_mul,eval_ofNat,eval_X,eval_one]

end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_InstanceDataProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.InstanceProgram
open Finset
abbrev Matrix := List (List ℚ)
end MetricKMedian.InstanceProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_SignedPreparationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.SparseSignedPreparation.Program
open SparseIntegerLaw.BinarySparse
abbrev QRow := List ℚ

end MetricKMedian.SparseSignedPreparation.Program
end

end OAI
end


