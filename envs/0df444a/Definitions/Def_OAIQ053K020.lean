-- Prove2me | Definitions.Def_OAIQ053K020
-- name    : OAIQ053K020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:56:50.761266+00:00
-- url     : https://prove2.me/theorems/cef322e3-b3a7-4967-a8ed-dbd0e1e1a572
-- title:
--   Definitions bundle OAIQ053K020 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 83 declarations of OpenAI's Lean: 48 definitions, 3 inductive types or structures, 1 instance and 31 theorems. The definitions and types are `OAI.MetricKMedian.FixedBatch.balancedActions`, `OAI.MetricKMedian.FixedBatch.balancedConflicts`, `OAI.MetricKMedian.FixedBatch.charge`, `OAI.MetricKMedian.FixedBatch.countErase`, `OAI.MetricKMedian.FixedBatch.countOpening`, `OAI.MetricKMedian.FixedBatch.nextCap`, `OAI.MetricKMedian.FractionalDual.bestThreshold`, `OAI.MetricKMedian.FractionalDual.gradient`, `OAI.MetricKMedian.Gaussian.IntegerProgram.Input.rational`, `OAI.MetricKMedian.Gaussian.IntegerProgram.Input.raw`, `OAI.MetricKMedian.Gaussian.IntegerProgram.Row`, `OAI.MetricKMedian.Gaussian.IntegerProgram.Rows`, `OAI.MetricKMedian.Gaussian.ListOperation.Audit`, `OAI.MetricKMedian.Gaussian.ListOperation.Input`, `OAI.MetricKMedian.Gaussian.ListOperation.Input.result`, `OAI.MetricKMedian.Gaussian.ListOperation.basis`, `OAI.MetricKMedian.Gaussian.ListOperation.coefficients`, `OAI.MetricKMedian.Gaussian.ListOperation.kernelList`, `OAI.MetricKMedian.Gaussian.ListOperation.lift`, `OAI.MetricKMedian.Gaussian.ListOperation.pivot`, `OAI.MetricKMedian.Gaussian.ListOperation.reduce`, `OAI.MetricKMedian.Gaussian.MatrixState`, `OAI.MetricKMedian.Gaussian.ResidualCertificate.initial`, `OAI.MetricKMedian.Gaussian.ResidualCertificate.pivot`, `OAI.MetricKMedian.Gaussian.kernelStates`, `OAI.MetricKMedian.GraphComparison.normalizedDrift`, `OAI.MetricKMedian.GraphComparison.unnormalizedDrift`, `OAI.MetricKMedian.Instance.indexedDistance`, `OAI.MetricKMedian.IntegerLaw.ListPivot.least`, `OAI.MetricKMedian.IntegerLaw.ListPivot.pivot`, `OAI.MetricKMedian.IntegerLaw.ListPivot.ratio`, `OAI.MetricKMedian.IntegerLaw.ListPivot.update`, `OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.Label`, `OAI.MetricKMedian.PhysicalPotential.potential`, `OAI.MetricKMedian.RationalBatchData.Ordinal.actionOrder`, `OAI.MetricKMedian.RationalBatchData.Ordinal.code`, `OAI.MetricKMedian.SparseBernoulli.Program.Context`, `OAI.MetricKMedian.SparseBernoulli.Program.Context.raw`, `OAI.MetricKMedian.SparseBernoulli.Program.T`, `OAI.MetricKMedian.SparseBernoulli.Program.endpoint` and 11 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Compression_AffineListOperations`, `KMedian_Compression_GaussianBinaryProgram`, `KMedian_Compression_GaussianInputBounds`, `KMedian_Compression_GaussianListOperations`, `KMedian_Compression_GaussianListPivot`, `KMedian_Compression_GaussianListSemantics`, `KMedian_Compression_GaussianListSize`, `KMedian_Compression_GaussianResidualCertificate`, `KMedian_Compression_GaussianStates`, `KMedian_Compression_IntegerKernelProgram`, `KMedian_Geometry_FixedBatchTransition`, `KMedian_Geometry_GraphComparison`, `KMedian_Instance`, `KMedian_Machines_AlphabetIndex`, `KMedian_Optimization_ApproximateLPSelection`, `KMedian_Optimization_FractionalDual`, `KMedian_Optimization_IndexedInstanceLP`, `KMedian_Optimization_SimplexDiameter`, `KMedian_Optimization_TruncatedObjective`, `KMedian_Optimization_TruncatedOptimization`, `KMedian_Probability_BernoulliListOperations`, `KMedian_Probability_BernoulliStepProgram`, `KMedian_Process_ActualActions`, `KMedian_Process_AveragedDrift`, `KMedian_Process_BatchOrdinalCodes`, `KMedian_Process_PhysicalBatchProgram`, `KMedian_Process_PhysicalPotential`, `KMedian_Process_RoundingStateCompiler`, `KMedian_Process_UnbalancedActions`, `KMedian_Programs_GraphLawProgram`, `KMedian_Programs_PivotListProgram`, `KMedian_Sparse_SparseBindProgram`, `KMedian_Sparse_SparseListTrim`.
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundles `OAIQ053K000`, `OAIQ053K001`, `OAIQ053K002`, `OAIQ053K003`, `OAIQ053K004`, `OAIQ053K005`, `OAIQ053K006`, `OAIQ053K007` and `OAIQ053K008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K033`, `OAIQ053K034` and `OAIQ053K035`; the statements `OAI.MetricKMedian.CopyState.balanced_count_change_s53`, `OAI.MetricKMedian.CopyState.rational_conditional_round_drift_s53`, `OAI.MetricKMedian.CopyState.unbalanced_count_change_s53`, `OAI.MetricKMedian.CopyState.unbalanced_small_change_s53`, `OAI.MetricKMedian.FixedBatch.forced_step_local_bound_s53`, `OAI.MetricKMedian.FixedBatch.masked_biased_linear_bound_s53`, `OAI.MetricKMedian.FixedBatch.masked_mass_sum_s53`, `OAI.MetricKMedian.FixedBatch.masked_total_bound_s53`, `OAI.MetricKMedian.FixedBatch.post_force_bound_s53`, `OAI.MetricKMedian.GeneratorAverage.expanded_bound_s53`, `OAI.MetricKMedian.PhysicalPotential.expected_time_advance_s53`, `OAI.MetricKMedian.SparseCopyState.physical_count_tail_s53` and `OAI.MetricKMedian.SparseEnumeratedFixedBatch.actual_local_bound_s53`; the proofs of `OAI.MetricKMedian.CopyState.balanced_count_change_s53`, `OAI.MetricKMedian.CopyState.rational_conditional_round_drift_s53`, `OAI.MetricKMedian.CopyState.unbalanced_count_change_s53`, `OAI.MetricKMedian.CopyState.unbalanced_small_change_s53`, `OAI.MetricKMedian.FixedBatch.forced_step_local_bound_s53`, `OAI.MetricKMedian.FixedBatch.masked_biased_linear_bound_s53`, `OAI.MetricKMedian.FixedBatch.masked_mass_sum_s53`, `OAI.MetricKMedian.FixedBatch.masked_total_bound_s53`, `OAI.MetricKMedian.FixedBatch.post_force_bound_s53`, `OAI.MetricKMedian.GeneratorAverage.averaged_ideal_drift_s53`, `OAI.MetricKMedian.GeneratorAverage.expanded_bound_s53`, `OAI.MetricKMedian.PhysicalPotential.expected_time_advance_s53`, `OAI.MetricKMedian.RationalBatchData.proposal_survival_s53` and `OAI.MetricKMedian.RationalPhysicalKernel.step_count_tail_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K000
import Definitions.Def_OAIQ053K001
import Definitions.Def_OAIQ053K002
import Definitions.Def_OAIQ053K003
import Definitions.Def_OAIQ053K004
import Definitions.Def_OAIQ053K005
import Definitions.Def_OAIQ053K006
import Definitions.Def_OAIQ053K007
import Definitions.Def_OAIQ053K008

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianListOperations
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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

def pivot (row : Row) : ℕ := row.findIdx (fun q => decide (q≠0))

def coefficients (row : Row) (p : ℕ) : Row := (erase row p).map (fun q => q/row[p]?.getD 0)

def reduce (c : Row) (p : ℕ) (row : Row) : Row :=
  ((erase row p).zip c).map (fun x => x.1-x.2*row[p]?.getD 0)

def lift (row : Row) (p : ℕ) (z : Row) : Row :=
  insert z p (-(((coefficients row p).zip z).map (fun x => x.1*x.2)).sum)

def basis (slots : List Unit) : Row :=
  if slots.isEmpty then [] else 1::slots.tail.map (fun _ => 0)

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
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianResidualCertificate
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianStates
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianListSize
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
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianInputBounds
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

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianListPivot
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianListSemantics
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Finset

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
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianBinaryProgram
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
-- module Solutions.OAIQ053_KM.KMedian_Compression_IntegerKernelProgram
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
end MetricKMedian.Gaussian.IntegerProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_AffineListOperations
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.IntegerLaw.ListOperation
open Binary Gaussian
open Finset

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

noncomputable def potential {I : Type*} (x g : ℝ) (d : I → ℝ) (S : Finset I) (b : ℝ) : ℝ :=
  (1 + m x + B x * mass g S) * cost g d S + (1 - mass g S) * b

end MetricKMedian.PhysicalPotential
end
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

noncomputable def nextCap (D : Actions I E) (d : I → ℝ) (bForce : ℝ) (A : Finset E) : ℝ :=
  (A ∩ D.ordinary).fold min bForce (fun e => d (D.source e))

noncomputable def charge (D : Actions I E) (x g b : ℝ) (d : I → ℝ) (S : Finset I) (e : E) : ℝ :=
  if e ∈ D.ordinary ∧ D.source e ∈ S then
    d (D.source e)-(∑ i ∈ S \ D.erase e, g*max (d (D.source e)-coefficient x (mass g S)*d i) 0)-
      potential x g d S b
  else
    mass g (S ∩ D.erase e)*min b (d (D.source e))-
      coefficient x (mass g S)*PhysicalPotential.cost g d (S ∩ D.erase e)-
      B x*mass g (S ∩ D.erase e)*(PhysicalPotential.cost g d S-PhysicalPotential.cost g d (S ∩ D.erase e))

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_GraphComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.GraphComparison

open FiniteComparison Analytic

noncomputable def normalizedDrift {I : Type*} [Fintype I]
    (π D N s : I → ℝ) (q K : I → I → ℝ) (x y pHat : ℝ) : ℝ :=
  -3-2*(P x*(y-x)^2/y)+average π (fun i =>
    (1-average π (q i))*(D i+(1-pHat*s i)*N i)+
    (1+m x+2*P x*y)*average π (q i)*D i+2*P x*y*average π (q i)+
    2*P x*average π (fun t => K i t*D t)-
    average π (fun t => (1-q i t)*max (D t-(1+m x+2*P x*y)*D i) 0))

end MetricKMedian.GraphComparison
end
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

theorem facilities_nonempty (I : Instance) : I.facilities.Nonempty :=
  card_pos.mp (I.k_pos.trans I.k_le)

end Instance
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_AlphabetIndex
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
abbrev Label := IncidenceReduction.Label
end MetricKMedian.PCP.Compiler.AlphabetProgram

end Inline_PCPAlphabetIndex

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_FractionalDual
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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

def bestThreshold (d y : ι → ℚ) (H : ℚ) : ℚ :=
  let U := (thresholds d H).filter (fun τ => affine d y τ=value d y H)
  if h : U.Nonempty then U.max' h else 0

theorem bestThreshold_spec (d y : ι → ℚ) (H : ℚ) :
    bestThreshold d y H ∈ thresholds d H ∧
      affine d y (bestThreshold d y H)=value d y H := by
  have hn : ((thresholds d H).filter (fun τ => affine d y τ=value d y H)).Nonempty := by
    obtain ⟨τ,hτ,he⟩ := mem_image.mp (max'_mem ((thresholds d H).image (affine d y))
      ((insert_nonempty 0 _).image _))
    exact ⟨τ,mem_filter.mpr ⟨hτ,he⟩⟩
  simp only [bestThreshold,dite_eq_left hn]
  exact mem_filter.mp (max'_mem _ hn)

def gradient (d y : ι → ℚ) (H : ℚ) (i : ι) : ℚ :=
  -max 0 (bestThreshold d y H-d i)

theorem gradient_spec (d y z : ι → ℚ) (H : ℚ) :
    value d y H-value d z H ≤ ∑ i, gradient d y H i*(y i-z i) := by
  obtain ⟨hτ,he⟩ := bestThreshold_spec d y H
  have hz := affine_le_value d z H (bestThreshold d y H) hτ
  rw [← he]
  have hid : affine d y (bestThreshold d y H)-affine d z (bestThreshold d y H)=
      ∑ i, gradient d y H i*(y i-z i) := by
    unfold affine gradient
    calc
      _ = (∑ i, z i*max 0 (bestThreshold d y H-d i))-
          (∑ i, y i*max 0 (bestThreshold d y H-d i)) := by ring
      _ = ∑ i, (z i*max 0 (bestThreshold d y H-d i)-y i*max 0 (bestThreshold d y H-d i)) := by
        rw [sum_sub_distrib]
      _ = _ := sum_congr rfl (fun _ _ => by ring)
  linarith

theorem gradient_bound (d y : ι → ℚ) (H : ℚ) (hH : 0 ≤ H)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ H) (i : ι) :
    |gradient d y H i| ≤ H := by
  have hmem := (bestThreshold_spec d y H).1
  have hτ : bestThreshold d y H ≤ H := by
    obtain he | hmem := mem_insert.mp hmem
    · rw [he]; exact hH
    · obtain he | hmem := mem_insert.mp hmem
      · exact he.le
      · obtain ⟨a,_,he⟩ := mem_image.mp hmem
        rw [← he]; exact (hd a).2
  unfold gradient
  rw [abs_neg,abs_of_nonneg (le_max_left _ _)]
  exact max_le hH (by linarith [(hd i).1])

end MetricKMedian.FractionalDual
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_SimplexDiameter
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ProjectedSubgradient
open Finset
variable {n : ℕ}

theorem initial_feasible [NeZero n] (k : ℚ) (hk : 0 ≤ k) : feasible k (point (initial (n:=n) k)) := by
  simp only [initial,point_ofFn]
  constructor
  · intro i
    dsimp only
    split_ifs
    · exact hk
    · exact le_rfl
  · rw [sum_ite_eq',ite_eq_left (mem_univ _)]

end MetricKMedian.ProjectedSubgradient
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

def objective (d : κ → ι → ℚ) (y : ι → ℚ) (H : ℚ) : ℚ :=
  ∑ j, FractionalDual.value (truncated d H j) y H

def gradient (d : κ → ι → ℚ) (y : ι → ℚ) (H : ℚ) (i : ι) : ℚ :=
  ∑ j, FractionalDual.gradient (truncated d H j) y H i

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_TruncatedOptimization
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
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

def optimize (d : Fin m → Fin n → ℚ) (r k H : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hH : 0 < H) : Vector ℚ n :=
  let T := steps (n:=n) (m:=m) r k H
  letI : NeZero T := ⟨(steps_pos r k H hr hk hH).ne'⟩
  let v := trajectory (k:ℚ) (rate (n:=n) (m:=m) r H)
    (fun y => gradient d y H) (initial (k:ℚ))
  let a := Preparation.firstNearest (univ:Finset (Fin T))
    (fun t => objective d (point (v t.val)) H) univ_nonempty
  v a.val

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_ApproximateLPSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset
variable {n m : ℕ} [NeZero n] [NeZero m]

instance instDecidableValid (out : FractionalData n m) (k : ℕ) : Decidable (out.Valid k) :=
  by unfold FractionalData.Valid; infer_instance

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_IndexedInstanceLP
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

def indexedDistance (I : Instance) (j : Fin I.clients.card) (i : Fin I.facilities.card) : ℚ :=
  I.distance (I.clients.orderEmbOfFin rfl j) (I.facilities.orderEmbOfFin rfl i)

theorem indexedDistance_nonneg (I : Instance) : ∀ j i, 0 ≤ I.indexedDistance j i :=
  fun _ _ => I.distance_nonneg _ _

end Instance
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliListOperations
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.SparseBernoulli.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly

 theorem flag_product {n : ℕ} (q : Fin n → Bool) (S : Finset (Fin n)) :
    (∏ i∈S, flag q i) = if ∀ i∈S, q i=true then 1 else 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi,ih]
    by_cases hq : q i=true <;> by_cases hs : ∀j∈S,q j=true <;> simp [flag,hq,hs]

 theorem get_true_iff {n : ℕ} (q : Fin n → Bool) (k : ℕ) :
    ((List.ofFn q)[k]?.getD true)=true ↔ ∀ i : Fin n, k=i.val → q i=true := by
  by_cases hk : k<n
  · simp only [List.getElem?_ofFn, dite_eq_left hk]
    simp only [Option.getD_some]
    constructor
    · intro h i hi
      have he : i=(⟨k,hk⟩ : Fin n) := Fin.ext hi.symm
      simpa only [he] using h
    · intro h; exact h ⟨k,hk⟩ rfl
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hk)]
    simp only [Option.getD_none,true_iff]
    intro i hi
    exact (hk (hi ▸ i.isLt)).elim

end MetricKMedian.SparseBernoulli.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_PivotListProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseListTrim
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingStateCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse

theorem trimData_map {α β : Type} (f : α → β) (d : Data α) :
    trimData (d.1,d.2.map f)=((trimData d).1,(trimData d).2.map f) := by
  have hz : d.1.2.zip (d.2.map f)=(d.1.2.zip d.2).map (fun z => (z.1,f z.2)) := by
    exact List.zip_map_right
  simp only [trimData,activeEntries,hz,List.filter_map,List.map_map,Function.comp_def]

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliStepProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseBernoulli.Program
open Binary Binary.PolyProgram Function
structure Context where
  input : Input
  t : ℕ
abbrev Context.raw (c : Context) := (List.ofFn c.input.p,c.t)
abbrev T (c : Context) := Fin c.input.n → Bool
abbrev view (c : Context) (q : T c) := List.ofFn q

def probability (c : Context) (_ : T c) : ℚ := if h : c.t < c.input.n then c.input.p ⟨c.t,h⟩ else 0
def endpoint (c : Context) (q : T c) (b : Fin 2) : T c :=
  fun i => if i.val=c.t then decide (b=0) else q i
 theorem probability_unit (c : Context) (q : T c) : 0 ≤ probability c q ∧ probability c q ≤ 1 := by
  unfold probability
  split_ifs with h
  · exact c.input.feasible _
  · norm_num

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_AveragedDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.GraphComparison

open FiniteComparison Analytic

noncomputable def unnormalizedDrift {I : Type*} [Fintype I]
    (μ d N s : I → ℝ) (q K : I → I → ℝ) (x y pHat : ℝ) : ℝ :=
  let V := ∑ i, μ i*d i
  let w := fun i => ∑ t, μ t*q i t
  let a := 1+m x+B x*y;
  -(3*y+B x*(y-x)^2)*V+
    ∑ i, μ i*((y-w i)*(d i+(1-pHat*s i)*N i)+a*w i*d i+B x*V*w i+
      B x*(∑ t, μ t*K i t*d t)-
      ∑ t, μ t*(1-q i t)*max (d t-a*d i) 0)

end MetricKMedian.GraphComparison
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_ActualActions
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential FiniteGraph
variable {I E : Type*} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

noncomputable def balancedActions (D : Actions I E) (Δ : ℕ) : Finset E :=
  D.ordinary.filter (fun e => (D.erase e).card=Δ)

noncomputable def balancedConflicts (D : Actions I E) (Δ : ℕ) (e : E) : Finset E :=
  if e ∈ balancedActions D Δ then conflicts D.erase (balancedActions D Δ) e else ∅

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_BatchOrdinalCodes
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.RationalBatchData.Ordinal
open Finset FixedBatch
open SparseGraph.ListOperation (Row indices)
variable {I : Type} [LinearOrder I] {n : ℕ}
variable (r : Fin n ≃o I) (D : Actions I I) (H : Finset I)

abbrev actionOrder : LinearOrder (HeavyAction D H) := by
  letI : LinearOrder (I × I) := pairOrder (I:=I)
  exact LinearOrder.lift' (fun e : HeavyAction D H => toLex e) (fun _ _ h => h)

def code : HeavyAction D H → ℕ
 | .inl h => (r.symm h.val).val
 | .inr p => n+(r.symm p.val.1).val*n+(r.symm p.val.2).val

 theorem code_strictMono : @StrictMono _ _ (actionOrder D H).toPreorder _ (code r D H) := by
  let : LinearOrder (I × I) := pairOrder (I:=I)
  let : LinearOrder (HeavyAction D H) := actionOrder D H
  intro e f hef
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      have hh := Sum.lex_inl_inl.mp hef
      exact r.symm.strictMono hh
    | inr f =>
      simp only [code]
      have he := (r.symm e.val).isLt
      omega
  | inr e =>
    cases f with
    | inl f => cases hef
    | inr f =>
      have hh := Sum.lex_inr_inr.mp hef
      change Prod.Lex (fun a b : I => a<b) (fun a b : I => a<b) e.val f.val at hh
      rcases Prod.lex_def.mp hh with h | ⟨h,h'⟩
      · have h1 : (r.symm e.val.1).val+1≤(r.symm f.val.1).val := r.symm.strictMono h
        have h2 := (r.symm e.val.2).isLt
        simp only [code]
        nlinarith
      · have h1 := congrArg (fun i => (r.symm i).val) h
        have h2 : (r.symm e.val.2).val<(r.symm f.val.2).val := r.symm.strictMono h'
        simp only [code]
        rw [h1]
        omega
 theorem code_lt (e : HeavyAction D H) : code r D H e<n+n*n := by
  cases e with
  | inl e => simp only [code]; have he := (r.symm e.val).isLt; omega
  | inr e =>
    simp only [code]
    have he := (r.symm e.val.1).isLt
    have hf := (r.symm e.val.2).isLt
    nlinarith
 theorem enumeration_strictMono [Fintype I] : StrictMono (fun i => code r D H (enumeration D H i)) := by
  let : LinearOrder (I × I) := pairOrder (I:=I)
  let : LinearOrder (HeavyAction D H) := actionOrder D H
  intro i j hij
  apply code_strictMono r D H
  exact @OrderIso.strictMono _ _ _ (actionOrder D H).toPreorder
    (@Fintype.orderIsoFinOfCardEq (HeavyAction D H) (actionOrder D H) _ _ rfl) i j hij
 theorem code_light (e : HeavyAction D H) : code r D H e<n ↔ e.isLeft=true := by
  cases e with
  | inl e => simp only [code,Fin.isLt,Sum.isLeft_inl]
  | inr e => simp only [code,Sum.isLeft_inr,Bool.false_eq_true,iff_false]; omega
end MetricKMedian.RationalBatchData.Ordinal
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

 theorem scaling_denominator_equiv {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (w : ι → ℚ) :
    RationalScaling.denominator (fun j => w (e.symm j))=RationalScaling.denominator w := by
  unfold RationalScaling.denominator
  exact e.symm.prod_comp (fun i => ((w i).den:ℤ))

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalBatchProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparsePhysicalBatch.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row )

def Input.bernInput (bal : Bool) (x : Input) : SparseBernoulli.Program.Input :=
  ⟨x.n,(fun i => if bal then x.p else x.q i),fun i => by cases bal <;> [exact x.hq i; exact x.hp]⟩
end MetricKMedian.SparsePhysicalBatch.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_UnbalancedActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential
variable {I E : Type*} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

noncomputable def countErase (D : Actions I E) (Δ : ℕ) (e : E) : Finset I :=
  if e ∈ balancedActions D Δ then ∅ else D.erase e

noncomputable def countOpening (D : Actions I E) (Δ : ℕ) (e : E) : ℝ :=
  if e ∈ D.ordinary ∧ e ∉ balancedActions D Δ then 1 else 0

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_GraphLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseGraph.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse

def QInput.column (x : QInput) (i : Fin x.m) : SparseBernoulli.Program.Input :=
  ⟨x.n,fun h => x.q h i,fun h => x.feasible h i⟩
def QInput.columns (x : QInput) : List SparseBernoulli.Program.Input := List.ofFn x.column
def emptyColumn : SparseBernoulli.Program.Input := ⟨0,Fin.elim0,fun i => Fin.elim0 i⟩
end MetricKMedian.SparseGraph.Program
end

end OAI
end


