-- Prove2me | Definitions.Def_OAIQ035K020
-- name    : OAIQ035K020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:56:38.296032+00:00
-- url     : https://prove2.me/theorems/fdd47144-e6ff-48d6-ac40-29d7213e982a
-- title:
--   Definitions bundle OAIQ035K020 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 48 declarations of OpenAI's Lean: 22 definitions, 3 inductive types or structures and 23 theorems. The definitions and types are `OAI.MetricKMedian.Gaussian.IntegerProgram.Input.rational`, `OAI.MetricKMedian.Gaussian.IntegerProgram.Input.raw`, `OAI.MetricKMedian.Gaussian.IntegerProgram.Row`, `OAI.MetricKMedian.Gaussian.IntegerProgram.Rows`, `OAI.MetricKMedian.Gaussian.IntegerProgram.castRows`, `OAI.MetricKMedian.Gaussian.ListOperation.FrameValid`, `OAI.MetricKMedian.Gaussian.ListOperation.FramesValid`, `OAI.MetricKMedian.Gaussian.ListOperation.Input`, `OAI.MetricKMedian.Gaussian.ListOperation.Input.raw`, `OAI.MetricKMedian.Gaussian.ListOperation.desc`, `OAI.MetricKMedian.Gaussian.MatrixState`, `OAI.MetricKMedian.Gaussian.ResidualCertificate.initial`, `OAI.MetricKMedian.Gaussian.ResidualCertificate.pivot`, `OAI.MetricKMedian.Gaussian.kernelStates`, `OAI.MetricKMedian.IntegerLaw.ListOperation.Input`, `OAI.MetricKMedian.IntegerLaw.ListOperation.Input.kernel`, `OAI.MetricKMedian.IntegerLaw.ListPivot.least`, `OAI.MetricKMedian.IntegerLaw.ListPivot.pivot`, `OAI.MetricKMedian.IntegerLaw.ListPivot.ratio`, `OAI.MetricKMedian.IntegerLaw.ListPivot.update`, `OAI.MetricKMedian.LPBinary.Nearest.entries`, `OAI.MetricKMedian.RoundingProgram.stateBound`, `OAI.MetricKMedian.SparseIntegerLaw.BinarySparse.activeEntries`, `OAI.MetricKMedian.SparseIntegerLaw.BinarySparse.branchLawData`, `OAI.MetricKMedian.SparseIntegerLaw.BinarySparse.trimData`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Compression_AffineElimination`, `KMedian_Compression_AffineListOperations`, `KMedian_Compression_ComputedElimination`, `KMedian_Compression_GaussianInputBounds`, `KMedian_Compression_GaussianListOperations`, `KMedian_Compression_GaussianListSemantics`, `KMedian_Compression_GaussianListSize`, `KMedian_Compression_GaussianResidualCertificate`, `KMedian_Compression_GaussianStates`, `KMedian_Compression_IntegerKernelProgram`, `KMedian_Geometry_TrimIntegerLaw`, `KMedian_Process_RoundingListOperations`, `KMedian_Process_RoundingRunProgram`, `KMedian_Programs_NearestListProgram`, `KMedian_Programs_PivotListProgram`, `KMedian_Sparse_SparseBranchProgram`, `KMedian_Sparse_SparseIterationHeight`, `KMedian_Sparse_SparseListTrim`.
--
--   **Imports.** It imports the bundles `OAIQ035K000`, `OAIQ035K001`, `OAIQ035K002`, `OAIQ035K003`, `OAIQ035K004`, `OAIQ035K005`, `OAIQ035K006`, `OAIQ035K007` and `OAIQ035K008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K031`, `OAIQ035K032`, `OAIQ035K034` and `OAIQ035K062`; the proofs of `OAI_MetricKMedian_CopyState_assignment_copies` and `OAI_MetricKMedian_RationalPhysicalKernel_histories_completed_expectation`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K000
import Definitions.Def_OAIQ035K001
import Definitions.Def_OAIQ035K002
import Definitions.Def_OAIQ035K003
import Definitions.Def_OAIQ035K004
import Definitions.Def_OAIQ035K005
import Definitions.Def_OAIQ035K006
import Definitions.Def_OAIQ035K007
import Definitions.Def_OAIQ035K008

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_AffineElimination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian
open Finset

namespace IntegerLaw
variable {Ω I : Type} [Fintype Ω] [Fintype I]

theorem numerator_le (μ : IntegerLaw Ω) (i : Ω) : μ.numerator i ≤ μ.denominator := by
  rw [← μ.total]
  exact single_le_sum (fun j _ => μ.numerator_nonneg j) (mem_univ i)

end IntegerLaw
end MetricKMedian

end OAI
end

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

 theorem erase_ofFn {n : ℕ} (f : Fin (n+1) → α) (p : Fin (n+1)) :
    erase (List.ofFn f) p.val=List.ofFn (fun j => f (p.succAbove j)) := by
  rw [erase_eq]
  have hl : ((List.ofFn f).eraseIdx p.val).length=n := by
    rw [List.length_eraseIdx_of_lt (by simpa using p.isLt),List.length_ofFn]
    omega
  apply List.ext_getElem (by simpa only [List.length_ofFn] using hl)
  intro i hi hj
  have hin : i<n := by simpa only [List.length_ofFn] using hj
  rw [List.getElem_eraseIdx]
  simp only [List.getElem_ofFn]
  by_cases hip : i<p.val
  · rw [dite_eq_left hip,Fin.succAbove_of_castSucc_lt _ _ (by exact hip)]
    rfl
  · rw [dite_eq_right hip,Fin.succAbove_of_le_castSucc _ _ (by exact Nat.le_of_not_gt hip)]
    rfl

 theorem coefficients_ofFn {n : ℕ} (f : Fin (n+1) → ℚ) (p : Fin (n+1)) :
    coefficients (List.ofFn f) p.val=List.ofFn (fun j => f (p.succAbove j)/f p) := by
  rw [coefficients,erase_ofFn,get_ofFn,List.map_ofFn]
  rfl

 theorem reduce_ofFn {n : ℕ} (f : Fin (n+1) → ℚ) (c : Fin n → ℚ) (p : Fin (n+1)) :
    reduce (List.ofFn c) p.val (List.ofFn f)=List.ofFn (fun j => f (p.succAbove j)-c j*f p) := by
  rw [reduce,erase_ofFn,get_ofFn,zip_ofFn,List.map_ofFn]
  rfl

 theorem residual_matrix {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ) (p : Fin (n+1)) :
    residual (List.ofFn (A 0)) p.val (matrix (fun i : Fin r => A i.succ))=
      matrix (Gaussian.residual A p) := by
  simp only [residual,matrix,List.map_ofFn,Function.comp_def,coefficients_ofFn,reduce_ofFn]
  rfl

 theorem insert_ofFn {n : ℕ} (f : Fin n → α) (p : Fin (n+1)) (a : α) :
    insert (List.ofFn f) p.val a=List.ofFn (p.insertNth a f) := by
  rw [insert_eq _ _ _ (by simp only [List.length_ofFn]; omega)]
  apply List.ext_getElem (by rw [List.length_insertIdx_of_le_length (by simp only [List.length_ofFn]; omega),List.length_ofFn,List.length_ofFn])
  intro i hi hj
  rw [List.getElem_insertIdx]
  simp only [List.getElem_ofFn]
  have hin : i<n+1 := by simpa only [List.length_ofFn] using hj
  by_cases hip : i<p.val
  · rw [dite_eq_left hip]
    have hsmall : i<n := by omega
    have he : p.succAbove (⟨i,hsmall⟩ : Fin n)=(⟨i,hin⟩ : Fin (n+1)) := by
      rw [Fin.succAbove_of_castSucc_lt _ _ (by exact hip)]
      rfl
    rw [← he,Fin.insertNth_apply_succAbove]
  · rw [dite_eq_right hip]
    by_cases hie : i=p.val
    · subst i
      rw [dite_eq_left rfl]
      simpa only using (Fin.insertNth_apply_same (α:=fun _ => α) p a f).symm
    · rw [dite_eq_right hie]
      have hsmall : i-1<n := by omega
      have he : p.succAbove (⟨i-1,hsmall⟩ : Fin n)=(⟨i,hin⟩ : Fin (n+1)) := by
        rw [Fin.succAbove_of_le_castSucc _ _ (by change p.val ≤ i - 1; omega)]
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      rw [← he,Fin.insertNth_apply_succAbove]

 theorem lift_ofFn {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ) (p : Fin (n+1)) (z : Fin n → ℚ) :
    lift (List.ofFn (A 0)) p.val (List.ofFn z)=List.ofFn (Gaussian.lift A p z) := by
  simp only [lift,coefficients_ofFn,zip_ofFn,List.map_ofFn,Function.comp_def,List.sum_ofFn,insert_ofFn,Gaussian.lift]

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

namespace ResidualCertificate
variable {R N r n : ℕ} {A : Fin R → Fin N → ℚ} {B : Fin r → Fin n → ℚ}

 theorem circuit (P : ResidualCertificate A B) (i : Fin r) :
    IsCircuit (fun c j => A j (P.pivotCols.orderEmbOfFin rfl c)) (P.coefficient i) := by
  intro v hv hk
  refine ⟨v (P.row i),P.decompose i v (fun j hj he => hv j (P.supported i j hj he)) ?_⟩
  intro j hj
  obtain ⟨c,hc⟩ := (P.pivotCols.orderIsoOfFin rfl).surjective ⟨j,hj⟩
  have he : P.pivotCols.orderEmbOfFin rfl c=j := congrArg Subtype.val hc
  simpa only [rowValue,he] using hk c

 def initial (A : Fin R → Fin N → ℚ) : ResidualCertificate A A where
  pivotRows := ∅
  pivotCols := ∅
  row := id
  col := id
  row_injective := Function.injective_id
  col_injective := Function.injective_id
  row_outside _ := (by simp)
  coefficient i j := if j=i then 1 else 0
  normalized _ := ite_eq_left rfl
  supported _ _ _ h := ite_eq_right h
  annihilates _ _ h := by simp at h
  represents i j := by simp [rowValue]
  independent v hv _ i := hv i ((by simp))

variable {B' : Fin (r+1) → Fin (n+1) → ℚ}

 def pivot (P : ResidualCertificate A B') (p : Fin (n+1)) (hp : B' 0 p ≠ 0) :
    ResidualCertificate A (residual B' p) where
  pivotRows := insert (P.row 0) P.pivotRows
  pivotCols := insert (P.col p) P.pivotCols
  row i := P.row i.succ
  col j := P.col (p.succAbove j)
  col_injective := P.col_injective.comp p.succAbove_right_injective
  row_injective := P.row_injective.comp (Fin.succ_injective _)
  row_outside i := by simp only [mem_insert,not_or]; exact ⟨P.next_row_ne i,P.row_outside _⟩
  coefficient i j := P.coefficient i.succ j-(B' i.succ p/B' 0 p)*P.coefficient 0 j
  normalized i := by rw [P.normalized,P.firstCoeff_next,mul_zero,sub_zero]
  supported i j hj he := by
    have hj' : j ∉ P.pivotRows := fun h => hj (mem_insert_of_mem h)
    have hj0 : j ≠ P.row 0 := fun h => hj (mem_insert.mpr (Or.inl h))
    rw [P.supported i.succ j hj' he,P.supported 0 j hj' hj0,mul_zero,sub_self]
  annihilates i j hj := by
    rw [rowValue_sub]
    rcases mem_insert.mp hj with he | he
    · subst j
      rw [← P.represents,← P.represents]
      field_simp
      ring
    · rw [P.annihilates _ _ he,P.annihilates _ _ he,mul_zero,sub_self]
  represents i j := by
    rw [rowValue_sub,← P.represents,← P.represents]
    dsimp only [residual]
    ring
  independent v hv hk := by
    have hd := P.decompose 0 v (by
      intro j hj he
      apply hv j
      simpa only [mem_insert,not_or] using And.intro he hj) (by
      intro j hj
      exact hk j (mem_insert_of_mem hj))
    have hve : v=(fun j => v (P.row 0)*P.coefficient 0 j) := funext hd
    have hkey := hk (P.col p) (mem_insert_self _ _)
    rw [hve,rowValue_smul,← P.represents] at hkey
    have hv0 : v (P.row 0)=0 := (mul_eq_zero.mp hkey).resolve_right hp
    intro j
    rw [hd j,hv0,zero_mul]

end ResidualCertificate
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

structure MatrixState where
  rows : ℕ
  cols : ℕ
  data : RatMatrix rows cols

def kernelStates : (r n : ℕ) → RatMatrix r n → List MatrixState
  | 0, n, A => [⟨0,n,A⟩]
  | r+1, 0, A => [⟨r+1,0,A⟩]
  | r+1, n+1, A =>
    ⟨r+1,n+1,A⟩ ::
    if h : (univ.filter (fun j => values A 0 j ≠ 0)).Nonempty then
      kernelStates r n (tabulate (residual (values A) ((univ.filter (fun j => values A 0 j ≠ 0)).min' h)))
    else kernelStates r (n+1) (tabulate (fun i j => values A i.succ j))

 theorem kernelStates_certificate {R N : ℕ} (original : Fin R → Fin N → ℚ)
    (r n : ℕ) (A : RatMatrix r n) (P : ResidualCertificate original (values A)) :
    ∀ B ∈ kernelStates r n A, Nonempty (ResidualCertificate original (values B.data)) := by
  induction r generalizing n with
  | zero =>
      intro B hB
      simp only [kernelStates,List.mem_singleton] at hB
      subst B
      exact ⟨P⟩
  | succ r ih =>
      cases n with
      | zero =>
          intro B hB
          simp only [kernelStates,List.mem_singleton] at hB
          subst B
          exact ⟨P⟩
      | succ n =>
          intro B hB
          rw [kernelStates,List.mem_cons] at hB
          rcases hB with rfl | hB
          · exact ⟨P⟩
          · split_ifs at hB with h
            · let p := (univ.filter (fun j => values A 0 j ≠ 0)).min' h
              have hp : values A 0 p ≠ 0 := (mem_filter.mp (min'_mem _ h)).2
              have PP : ResidualCertificate original (values (tabulate (residual (values A) p))) := by
                rw [values_tabulate]
                exact P.pivot p hp
              exact ih n _ PP B hB
            · have PP : ResidualCertificate original (values (tabulate (fun i j => values A i.succ j))) := by
                rw [values_tabulate]
                exact P.skip
              exact ih (n+1) _ PP B hB

 theorem kernelStates_underdetermined (r n : ℕ) (A : RatMatrix r n) (hn : r<n) :
    ∀ B ∈ kernelStates r n A, B.rows<B.cols := by
  induction r generalizing n with
  | zero =>
      intro B hB
      simp only [kernelStates,List.mem_singleton] at hB
      subst B
      exact hn
  | succ r ih =>
      cases n with
      | zero => omega
      | succ n =>
          intro B hB
          rw [kernelStates,List.mem_cons] at hB
          rcases hB with rfl | hB
          · exact hn
          · split_ifs at hB with h
            · exact ih n _ (by omega) _ hB
            · exact ih (n+1) _ (by omega) _ hB

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

def FrameValid (N H : ℕ) (f : Frame) : Prop :=
  f.1  ≤  N ∧ f.2.length  ≤  N ∧ ∀ q∈f.2, HasHeight q H
def FramesValid (N H : ℕ) (fs : Frames) : Prop := ∀ f∈fs, FrameValid N H f

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

structure Input where
  rows : ℕ
  cols : ℕ
  data : RatMatrix rows cols
  underdetermined : rows < cols

def Input.raw (I : Input) : List Unit × Rows :=
  (List.replicate I.cols (),matrix (values I.data))
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

def desc (r n : ℕ) (A : RatMatrix r n) (fs : Frames) : State :=
  .inl ((List.replicate n (),matrix (values A)),fs)

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
abbrev Row := IntegerList.Row
abbrev Rows := IntegerList.Rows

def Input.raw (I : Input) : List Unit × Rows :=
  (List.replicate I.n (),List.ofFn (fun i => List.ofFn (I.V i)))

def Input.rational (I : Input) : ListOperation.Input :=
  ⟨I.r,I.n,tabulate (fun i j => (I.V i j:ℚ)),I.underdetermined⟩
def castRows (vs : Rows) : ListOperation.Rows := vs.map (List.map (fun z : ℤ => (z:ℚ)))

theorem castRows_ofFn {r n : ℕ} (V : Fin r → Fin n → ℤ) :
    castRows (List.ofFn (fun i => List.ofFn (V i)))=ListOperation.matrix (fun i j => (V i j:ℚ)) := by
  simp only [castRows,List.map_ofFn,Function.comp_def,ListOperation.matrix]

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

structure Input where
  n : ℕ
  d : ℕ
  μ : IntegerLaw (Fin n)
  v : Fin n → Fin d → ℤ
  large : d+1 < μ.support.card

def Input.kernel (I : Input) : Gaussian.IntegerProgram.Input :=
  ⟨I.d+1,I.μ.support.card,activeMatrix I.μ I.v,I.large⟩

theorem range_ofFn {n : ℕ} {α : Type} (f : Fin n → α) :
    (List.range n).zip (List.ofFn f)=List.ofFn (fun i => (i.val,f i)) := by
  rw [indices_ofFn,Gaussian.ListOperation.zip_ofFn]

theorem extend_ofFn {n : ℕ} (s : Finset (Fin n)) (z : Fin s.card → ℤ) (i : Fin n) :
    extend (List.ofFn (fun j => (((s.orderIsoOfFin rfl) j).val.val,z j))) i.val=
      Compression.extendVector s z i := by
  unfold extend
  have he : ∀ xs : List (ℕ × ℤ), ((xs.filter (fun e => decide (e.1=i.val))).map Prod.snd).sum=
      (xs.map (fun e => if e.1=i.val then e.2 else 0)).sum := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a xs ih => by_cases h : a.1=i.val <;> simp [h,ih]
  rw [he,List.map_ofFn,List.sum_ofFn]
  by_cases hi : i∈s
  · let k : Fin s.card := (s.orderIsoOfFin rfl).symm ⟨i,hi⟩
    have hik : ((s.orderIsoOfFin rfl) k).val=i := congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨i,hi⟩)
    have hh (j : Fin s.card) : ((s.orderIsoOfFin rfl) j).val.val=i.val ↔ j=k := by
      constructor
      · intro h
        apply (s.orderIsoOfFin rfl).injective
        apply Subtype.ext
        exact (Fin.ext h).trans hik.symm
      · rintro rfl
        exact congrArg Fin.val hik
    simp only [Function.comp_apply,hh,Finset.sum_ite_eq',mem_univ,ite_true,Compression.extendVector,dite_eq_left hi]
    rfl
  · have hh (j : Fin s.card) : ((s.orderIsoOfFin rfl) j).val.val ≠ i.val := by
      intro h
      exact hi ((Fin.val_inj.mp h) ▸ ((s.orderIsoOfFin rfl) j).property)
    simp only [Function.comp_apply,hh,ite_false,sum_const_zero,Compression.extendVector,dite_eq_right hi]

end MetricKMedian.IntegerLaw.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_ComputedElimination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

theorem eliminateAt_preserves {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℚ) (z : Fin n → ℤ) (p : Fin n)
    (hp : 0 < z p) (hmin : ∀ i, 0 < z i → ratio μ z p ≤ ratio μ z i)
    (hzsum : ∑ i, z i=0) (hzmoment : ∀ j, ∑ i, (z i:ℚ)*v i j=0)
    (hzsupport : ∀ i, μ.numerator i=0 → z i=0) :
    let ν := eliminateAt μ z p hp hmin hzsum
    ν.numerator p=0 ∧ μ.numerator p ≠ 0 ∧
      (∀ i, μ.numerator i=0 → ν.numerator i=0) ∧
      ν.support ⊆ μ.support.erase p ∧
      ∀ j, (∑ i, ν.rational.weight i*v i j)=∑ i, μ.rational.weight i*v i j := by
  dsimp only
  have hz : (eliminateAt μ z p hp hmin hzsum).numerator p=0 := by
    rw [eliminateAt_numerator,sub_self]
  have hn : μ.numerator p ≠ 0 := by intro hp0; exact hp.ne' (hzsupport p hp0)
  have hs : ∀ i, μ.numerator i=0 → (eliminateAt μ z p hp hmin hzsum).numerator i=0 := by
    intro i hi
    rw [eliminateAt_numerator,hi,hzsupport i hi]
    ring
  refine ⟨hz,hn,hs,?_,?_⟩
  · intro i hi
    have hni := (mem_support _ i).mp hi
    apply mem_erase.mpr
    refine ⟨?_,(μ.mem_support i).mpr ?_⟩
    · intro he; subst i; exact hni hz
    · intro he; exact hni (hs i he)
  · intro j
    have hD : (μ.denominator:ℚ) ≠ 0 := by exact_mod_cast μ.denominator_pos.ne'
    have hpQ : (z p:ℚ) ≠ 0 := by exact_mod_cast hp.ne'
    change (∑ i, (((eliminateAt μ z p hp hmin hzsum).numerator i:ℚ)/
        ((μ.denominator*z p:ℤ):ℚ))*v i j)=_
    simp only [eliminateAt_numerator,Int.cast_mul,Int.cast_sub]
    have heq : ∀ i, (((μ.numerator i:ℚ)*(z p:ℚ)-(μ.numerator p:ℚ)*(z i:ℚ))/
        ((μ.denominator:ℚ)*(z p:ℚ)))*v i j=
        ((μ.numerator i:ℚ)*v i j)/(μ.denominator:ℚ)-
        ((μ.numerator p:ℚ)/(μ.denominator:ℚ)/(z p:ℚ))*((z i:ℚ)*v i j) := by
      intro i
      field_simp
    simp only [heq,sum_sub_distrib,← mul_sum,hzmoment,mul_zero,sub_zero]
    apply sum_congr rfl
    intro i _
    dsimp only [rational]
    ring

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_TrimIntegerLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

theorem trim_moment {n : ℕ} (μ : IntegerLaw (Fin n)) (f : Fin n → ℚ) :
    (∑ i, μ.trim.rational.weight i*f (μ.support.orderEmbOfFin rfl i))=
      ∑ i, μ.rational.weight i*f i := by
  simp only [trim_weight]
  calc
    _ = ∑ i : μ.support, μ.rational.weight i*f i :=
      Equiv.sum_comp (μ.support.orderIsoOfFin rfl).toEquiv _
    _ = ∑ i ∈ μ.support, μ.rational.weight i*f i := sum_coe_sort μ.support (fun i => μ.rational.weight i*f i)
    _ = _ := by
      apply sum_subset (subset_univ _)
      intro i _ hi
      have hz : μ.numerator i=0 := not_not.mp (by simpa only [mem_support] using hi)
      simp only [rational,hz,Int.cast_zero,zero_div,zero_mul]

end MetricKMedian.IntegerLaw

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

theorem fractional_list {n : ℕ} (p : Vector ℚ n) :
    fractional p.toList=((RationalWeightedStep.fractional p).sort).map Fin.val := by
  simp only [fractional,indices,Vector.length_toList,range_finRange,List.filter_map]
  unfold RationalWeightedStep.fractional
  rw [← EncodingLists.filter_range]
  apply congrArg (List.map Fin.val)
  apply List.filter_congr
  intro index _
  simp [frac, RationalWeightedStep.point]

theorem active_list {n : ℕ} (p : Vector ℚ n) :
    active p.toList=decide (1<(RationalWeightedStep.fractional p).card) := by
  simp only [active,fractional_list,List.length_map,Finset.length_sort]

theorem first_list {n : ℕ} (p : Vector ℚ n) (h : 1<(RationalWeightedStep.fractional p).card) :
    first p.toList=(RationalWeightedStep.pair p h).val.1.val := by
  unfold first indices
  rw [Vector.length_toList]
  apply findIdx_min
  · exact card_pos.mp (by omega)
  intro i
  simp [frac,RationalWeightedStep.fractional,RationalWeightedStep.point]

theorem get_point {n : ℕ} (p : Vector ℚ n) (i : Fin n) : p.toList[i.val]?.getD 0=point p i := by simp [point]

end MetricKMedian.RoundingList
end

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

def ratio (e : Entry) : ℚ := (e.1:ℚ)/(e.2:ℚ)
def least (es : List Entry) : ℚ := LPBinary.minimum (((es.filter (fun e => decide (0<e.2))).map ratio))
def pivot (es : List Entry) : ℕ := es.findIdx (fun e => decide (0<e.2 ∧ ratio e=least es))

def update (μ : LawData) (z : Row) : LawData :=
  let es := μ.2.zip z
  let p := pivot es
  let b := es[p]?.getD (0,0)
  (μ.1*b.2,es.map (fun e => e.1*b.2-b.1*e.2))

end MetricKMedian.IntegerLaw.ListPivot
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseListTrim
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.PolyProgram Function Finset
variable {α : Type}

def activeEntries (x : Data α) : List (ℤ × α) :=
  (x.1.2.zip x.2).filter (fun z => decide (z.1≠0))
def trimData (x : Data α) : Data α :=
  ((x.1.1,(activeEntries x).map Prod.fst),(activeEntries x).map Prod.snd)

end MetricKMedian.SparseIntegerLaw.BinarySparse
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

namespace MetricKMedian.SparseWeightedPartial
open Binary RationalWeightedStep
variable {n : ℕ}
theorem features_height (p : Vector ℚ n) (L : ℕ) (hp : ∀ i, HasHeight (point p i) L)
    (a : Fin (n+n*n)) : HasHeight (features p a) (2*L) := by
  unfold features
  generalize finSumFinEquiv.symm a=z
  cases z with
  | inl i => exact (hp i).mono (by omega)
  | inr ij => simpa only [Sum.elim_inr,← two_mul] using (hp (finProdFinEquiv.symm ij).1).mul (hp (finProdFinEquiv.symm ij).2)
end MetricKMedian.SparseWeightedPartial

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
open Binary Binary.PolyProgram Function
variable {α γ : Type}

def branchLawData (x : LawData × List ℚ) : LawData :=
  let D := IntegerList.denominator x.2
  let zs := IntegerList.numerators x.2
  (x.1.1*D,(x.1.2.zip zs).flatMap (fun z => [z.1*z.2,z.1*(D-z.2)]))

end MetricKMedian.SparseIntegerLaw.BinarySparse
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
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.BinarySparse

def stateBound (L : ℕ) :=
  2*L+1+ (2*(2*(heightBound L+4)+1+supportBound L*(2*(heightBound L+4)+1))+1+
    supportBound L*(2*(L*(2*(3*coordinateBound L+10)+1))+1))

theorem statePolynomial_eval (L : ℕ) : statePolynomial.eval L=stateBound L := by
  simp only [statePolynomial,stateBound,heightBound,coordinateBound,supportBound,CPoly,NPoly,HPoly,
    RoundingHeight.stepHeight,SparseIntegerLaw.stepHeight,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_NearestListProgram
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

end Nearest
end MetricKMedian.LPBinary
end

end OAI
end


