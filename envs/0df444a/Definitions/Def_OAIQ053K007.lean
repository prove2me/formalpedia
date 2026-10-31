-- Prove2me | Definitions.Def_OAIQ053K007
-- name    : OAIQ053K007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:53:51.080025+00:00
-- url     : https://prove2.me/theorems/dd17e74b-8299-4448-aba0-c44125336ed6
-- title:
--   Definitions bundle OAIQ053K007 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 131 declarations of OpenAI's Lean: 79 definitions, 3 inductive types or structures and 49 theorems. The definitions and types are `OAI.MetricKMedian.Gaussian.IntegerProgram.Input`, `OAI.MetricKMedian.Gaussian.ListOperation.erase`, `OAI.MetricKMedian.Gaussian.ListOperation.eu`, `OAI.MetricKMedian.Gaussian.ListOperation.frameBound`, `OAI.MetricKMedian.Gaussian.ListOperation.framesBound`, `OAI.MetricKMedian.Gaussian.ListOperation.insert`, `OAI.MetricKMedian.Gaussian.ListOperation.matrixBound`, `OAI.MetricKMedian.Gaussian.ListOperation.residualPolynomial`, `OAI.MetricKMedian.Gaussian.ListOperation.returnPolynomial`, `OAI.MetricKMedian.Gaussian.ListOperation.rowBound`, `OAI.MetricKMedian.Gaussian.ListOperation.stateBound`, `OAI.MetricKMedian.Gaussian.ListOperation.statePolynomial`, `OAI.MetricKMedian.Gaussian.ResidualCertificate`, `OAI.MetricKMedian.Gaussian.ResidualCertificate.skip`, `OAI.MetricKMedian.Gaussian.residualHeight`, `OAI.MetricKMedian.Gaussian.returnHeight`, `OAI.MetricKMedian.Gaussian.rowValue`, `OAI.MetricKMedian.GeneratorAverage.external`, `OAI.MetricKMedian.GeneratorAverage.inside`, `OAI.MetricKMedian.GraphComparison.externalMass`, `OAI.MetricKMedian.GraphComparison.externalSquare`, `OAI.MetricKMedian.GraphComparison.kernel`, `OAI.MetricKMedian.GraphComparison.rowType`, `OAI.MetricKMedian.GraphLaw.edge`, `OAI.MetricKMedian.GraphMoments.kernel`, `OAI.MetricKMedian.GraphMoments.removedCost`, `OAI.MetricKMedian.GraphMoments.removedMass`, `OAI.MetricKMedian.GroupCap.cap`, `OAI.MetricKMedian.InputParser.State`, `OAI.MetricKMedian.InputParser.parseStep`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.QRow`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.QRows`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.height`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.heightPolynomial`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.statePolynomial`, `OAI.MetricKMedian.IntegerLaw.ListOperation.extend`, `OAI.MetricKMedian.LPBinary.Repair.bounded`, `OAI.MetricKMedian.Normalization.matrixGuesses`, `OAI.MetricKMedian.PhysicalPotential.cost`, `OAI.MetricKMedian.ProjectedSubgradient.feasible` and 42 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Binary_InstanceParserProgram`, `KMedian_Binary_SequentialParserProgram`, `KMedian_Compression_AffineListOperations`, `KMedian_Compression_CompressionBounds`, `KMedian_Compression_GaussianInputBounds`, `KMedian_Compression_GaussianListCompiler`, `KMedian_Compression_GaussianListOperations`, `KMedian_Compression_GaussianListSize`, `KMedian_Compression_GaussianResidualCertificate`, `KMedian_Compression_GaussianResidualHeight`, `KMedian_Compression_GaussianStates`, `KMedian_Compression_IntegerKernelProgram`, `KMedian_Compression_RationalKernelHeightSupport`, `KMedian_Geometry_GraphComparison`, `KMedian_Geometry_GraphLaw`, `KMedian_Geometry_GraphMoments`, `KMedian_Geometry_GraphRunHeight`, `KMedian_Geometry_ListSigma`, `KMedian_Optimization_ApproximateFractional`, `KMedian_Optimization_FractionalListChecks`, `KMedian_Optimization_GradientDenominator`, `KMedian_Optimization_MatrixNormalization`, `KMedian_Optimization_ProjectedSubgradient`, `KMedian_Optimization_SimplexDiameter`, `KMedian_Optimization_SimplexProjection`, `KMedian_Optimization_TruncatedObjective`, `KMedian_Optimization_TruncatedOptimization`, `KMedian_Probability_BernoulliRunHeight`, `KMedian_Probability_BernoulliRunProgram`, `KMedian_Process_BatchOrdinalCodes`, `KMedian_Process_GeneratorAverage`, `KMedian_Process_GroupCap`, `KMedian_Process_PhysicalBatchProgram`, `KMedian_Process_PhysicalPotential`, `KMedian_Process_RoundingCoordinateHeight`, `KMedian_Process_RoundingListOperations`, `KMedian_Process_RoundingRunHeight`, `KMedian_Process_RoundingRunProgram`, `KMedian_Programs_GraphRunProgram`, `KMedian_Programs_RationalFeatureProgram`, `KMedian_Rounding_SignedListOperations`, `KMedian_Rounding_WeightedGridInvariant`, `KMedian_Sparse_SparseBranchProgram`, `KMedian_Sparse_SparseIterationHeight`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K019`, `OAIQ053K020`, `OAIQ053K021` and `OAIQ053K022`; the statements `OAI.MetricKMedian.FixedBatch.RationalParameters.selectCompleted_spec_s53`, `OAI.MetricKMedian.GeneratorAverage.averaged_ideal_drift_s53` and `OAI.MetricKMedian.RationalPhysicalKernel.graph_data_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_SequentialParserProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.InputParser
open Polynomial
section Generic
variable {α : Type}
  [Inhabited α]
  (read : List Bool → α × List Bool)
abbrev State := List Bool × List α
def parseStep (x : State (α:=α) × Unit) : State (α:=α) :=
  let s := read x.1.1
  (s.2,s.1::x.1.2)
end Generic
end MetricKMedian.InputParser
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_SimplexProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Simplex
open Finset
variable {ι : Type} [Fintype ι] [Nonempty ι]

def upper (x : ι → ℚ) (a : ι) : Finset ι := univ.filter (fun i => x a ≤ x i)

omit [Nonempty ι] in
theorem mem_upper_self (x : ι → ℚ) (a : ι) : a ∈ upper x a := by simp [upper]

omit [Nonempty ι] in
theorem upper_card_pos (x : ι → ℚ) (a : ι) : 0 < (upper x a).card :=
  card_pos.mpr ⟨a,mem_upper_self x a⟩

def threshold (x : ι → ℚ) (k : ℚ) (a : ι) : ℚ :=
  ((∑ i ∈ upper x a, x i)-k)/(upper x a).card

def level (x : ι → ℚ) (k : ℚ) : ℚ :=
  (univ.image (threshold x k)).max' (univ_nonempty.image _)

def project (x : ι → ℚ) (k : ℚ) (i : ι) : ℚ := max 0 (x i-level x k)

theorem threshold_le_level (x : ι → ℚ) (k : ℚ) (a : ι) :
    threshold x k a ≤ level x k :=
  le_max' _ _ (mem_image.mpr ⟨a,mem_univ _,rfl⟩)

theorem level_attained (x : ι → ℚ) (k : ℚ) : ∃ a, level x k=threshold x k a := by
  obtain ⟨a,_,ha⟩ := mem_image.mp (max'_mem (univ.image (threshold x k))
    (univ_nonempty.image _))
  exact ⟨a,ha.symm⟩

omit [Nonempty ι] in
theorem threshold_sum (x : ι → ℚ) (k : ℚ) (a : ι) :
    ∑ i ∈ upper x a, (x i-threshold x k a)=k := by
  have hc : ((upper x a).card:ℚ) ≠ 0 := by exact_mod_cast (upper_card_pos x a).ne'
  simp only [sum_sub_distrib,sum_const,nsmul_eq_mul,threshold]
  field_simp
  ring

theorem project_nonneg (x : ι → ℚ) (k : ℚ) (i : ι) : 0 ≤ project x k i := le_max_left _ _

end MetricKMedian.Simplex
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_ProjectedSubgradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ProjectedSubgradient
open Finset
variable {n : ℕ} [NeZero n]

abbrev point (v : Vector ℚ n) : Fin n → ℚ := fun i => v[i.val]

def sqdist (x y : Fin n → ℚ) : ℚ := ∑ i, (x i-y i)^2

omit [NeZero n] in
theorem sqdist_nonneg (x y : Fin n → ℚ) : 0 ≤ sqdist x y :=
  sum_nonneg (fun _ _ => sq_nonneg _)

omit [NeZero n] in
@[simp] theorem point_ofFn (f : Fin n → ℚ) : point (Vector.ofFn f)=f := by
  funext i
  simp only [point,Vector.getElem_ofFn]

omit [NeZero n] in
@[simp] theorem point_ofFn_apply (f : Fin n → ℚ) (i : Fin n) : point (Vector.ofFn f) i=f i := by
  simp only [point,Vector.getElem_ofFn]

def next (k η : ℚ) (g : (Fin n → ℚ) → Fin n → ℚ) (v : Vector ℚ n) : Vector ℚ n :=
  let w := Vector.ofFn (fun i => point v i-η*g (point v) i)
  let L := Simplex.level (point w) k
  Vector.ofFn (fun i => max 0 (point w i-L))

@[simp] theorem next_apply (k η : ℚ) (g : (Fin n → ℚ) → Fin n → ℚ)
    (v : Vector ℚ n) (i : Fin n) :
    point (next k η g v) i=Simplex.project (fun a => point v a-η*g (point v) a) k i := by
  simp only [next,point_ofFn_apply,point_ofFn,Simplex.project]

def trajectory (k η : ℚ) (g : (Fin n → ℚ) → Fin n → ℚ)
    (v : Vector ℚ n) : ℕ → Vector ℚ n
  | 0 => v
  | t+1 => next k η g (trajectory k η g v t)

@[simp] theorem trajectory_zero (k η : ℚ) (g : (Fin n → ℚ) → Fin n → ℚ)
    (v : Vector ℚ n) : trajectory k η g v 0=v := rfl

@[simp] theorem trajectory_succ (k η : ℚ) (g : (Fin n → ℚ) → Fin n → ℚ)
    (v : Vector ℚ n) (t : ℕ) :
    trajectory k η g v (t+1)=next k η g (trajectory k η g v t) := rfl

def feasible (k : ℚ) (x : Fin n → ℚ) : Prop := (∀ i, 0 ≤ x i) ∧ ∑ i, x i=k

end MetricKMedian.ProjectedSubgradient
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_SimplexDiameter
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

def initial [NeZero n] (k : ℚ) : Vector ℚ n := Vector.ofFn (fun i => if i=0 then k else 0)

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

def truncated (d : κ → ι → ℚ) (H : ℚ) (j : κ) (i : ι) : ℚ :=
  if d j i ≤ 1 then d j i else H

omit [Fintype ι] [Fintype κ] in
theorem truncated_bounds (d : κ → ι → ℚ) (H : ℚ)
    (hH : 1 ≤ H) (hd : ∀ j i, 0 ≤ d j i) (j : κ) (i : ι) :
    0 ≤ truncated d H j i ∧ truncated d H j i ≤ H := by
  unfold truncated
  split_ifs with hi
  · exact ⟨hd j i,hi.trans hH⟩
  · exact ⟨(by linarith),le_rfl⟩

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_TruncatedOptimization
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

def gradSize (H : ℕ) : ℕ := n*(m*H)^2

def steps (r k H : ℕ) : ℕ := 8*r^2*(gradSize (n:=n) (m:=m) H)*k^2

def rate (r H : ℕ) : ℚ := 1/(2*(r:ℚ)*(gradSize (n:=n) (m:=m) H:ℚ))

theorem gradSize_pos (H : ℕ) (hH : 0 < H) : 0 < gradSize (n:=n) (m:=m) H := by
  unfold gradSize
  exact Nat.mul_pos (NeZero.pos n) (pow_pos (Nat.mul_pos (NeZero.pos m) hH) _)

theorem steps_pos (r k H : ℕ) (hr : 0 < r) (hk : 0 < k) (hH : 0 < H) :
    0 < steps (n:=n) (m:=m) r k H := by
  unfold steps
  have hg := gradSize_pos (n:=n) (m:=m) H hH
  positivity

theorem rate_pos (r H : ℕ) (hr : 0 < r) (hH : 0 < H) :
    0 < rate (n:=n) (m:=m) r H := by
  unfold rate
  exact one_div_pos.mpr (mul_pos (mul_pos (by norm_num) (by exact_mod_cast hr))
    (by exact_mod_cast gradSize_pos (n:=n) (m:=m) H hH))

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_ApproximateFractional
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

def penalty (r k : ℕ) : ℕ := 4*r*(k+1)

def loss (r k : ℕ) : ℚ := (1+1/(r:ℚ))/(penalty r k:ℚ)

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_MatrixNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Normalization
open Finset
variable {m n : ℕ}

def matrixGuesses (d : Fin m → Fin n → ℚ) : Finset ℚ :=
  (univ : Finset (Fin m × Fin n)).biUnion (fun a =>
    if 0 < d a.1 a.2 then
      (range (m.size+1)).image (fun t => d a.1 a.2*(2:ℚ)^t)
    else ∅)

end MetricKMedian.Normalization
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_GradientDenominator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalGrid
open Finset

def At (D : ℤ) (q : ℚ) : Prop := ∃ a : ℤ, q=(a:ℚ)/(D:ℚ)

theorem zero (D : ℤ) : At D 0 := ⟨0,by simp⟩

theorem integer (D a : ℤ) (hD : D ≠ 0) : At D (a:ℚ) := by
  refine ⟨a*D,?_⟩
  rw [Int.cast_mul,mul_div_cancel_right₀ _ (by exact_mod_cast hD)]

theorem sub {D : ℤ} {a b : ℚ} (ha : At D a) (hb : At D b) : At D (a-b) := by
  obtain ⟨A,rfl⟩ := ha
  obtain ⟨B,rfl⟩ := hb
  exact ⟨A-B,by rw [Int.cast_sub,sub_div]⟩

end MetricKMedian.RationalGrid

end
end

end OAI
end

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

def erase (as : List α) (p : ℕ) := as.take p++(as.drop p).tail

def insert (as : List α) (p : ℕ) (a : α) := as.take p++a::as.drop p

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

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_GraphLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian

namespace GraphLaw
variable {I H : Type*} [Fintype I] [Fintype H] [DecidableEq I] [DecidableEq H]

noncomputable def edge (G : I → Finset H) (h : H) (i : I) : ℝ := if h ∈ G i then 1 else 0

end GraphLaw
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingListOperations
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
-- module Solutions.OAIQ053_KM.KMedian_Rounding_SignedListOperations
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
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianListCompiler
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
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianResidualCertificate
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
-- module Solutions.OAIQ053_KM.KMedian_Compression_RationalKernelHeightSupport
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
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianResidualHeight
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
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianStates
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
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianListSize
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
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianInputBounds
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
-- module Solutions.OAIQ053_KM.KMedian_Compression_IntegerKernelProgram
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
-- module Solutions.OAIQ053_KM.KMedian_Compression_AffineListOperations
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
-- module Solutions.OAIQ053_KM.KMedian_Compression_CompressionBounds
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
-- module Solutions.OAIQ053_KM.KMedian_Programs_RationalFeatureProgram
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
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBranchProgram
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
-- module Solutions.OAIQ053_KM.KMedian_Geometry_ListSigma
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
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalPotential
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
-- module Solutions.OAIQ053_KM.KMedian_Geometry_GraphMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian

namespace GraphMoments

variable {Ω I H : Type*} [Fintype Ω] [Fintype I] [Fintype H] [DecidableEq I]

noncomputable def removedMass (g : ℝ) (X : Ω → H → I → ℝ) (ω : Ω) (h : H) : ℝ :=
  ∑ i, g*X ω h i
noncomputable def removedCost (g : ℝ) (d : I → ℝ) (X : Ω → H → I → ℝ)
    (ω : Ω) (h : H) : ℝ := ∑ i, g*d i*X ω h i
noncomputable def kernel (g : ℝ) (q : H → I → ℝ) (i t : I) : ℝ :=
  ∑ h, g*q h i*q h t

end GraphMoments
end MetricKMedian
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

noncomputable def externalMass {I H : Type*} [Fintype H] (ρ : H → ℝ) (q : I → H → ℝ) (i : I) : ℝ :=
  ∑ h, ρ h*q i h
noncomputable def externalSquare {I H : Type*} [Fintype H] (ρ : H → ℝ) (q : I → H → ℝ) (i : I) : ℝ :=
  ∑ h, ρ h*(q i h)^2
noncomputable def rowType {I H : Type*} [Fintype H] (ρ : H → ℝ) (q : I → H → ℝ) (i : I) : ℝ :=
  externalSquare ρ q i/externalMass ρ q i
noncomputable def kernel {I H : Type*} [Fintype H] (ρ : H → ℝ) (q : I → H → ℝ) (i t : I) : ℝ :=
  ∑ h, ρ h*q i h*q t h

end MetricKMedian.GraphComparison
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_GeneratorAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.GeneratorAverage
open GraphComparison GraphMoments

variable {Ω I H : Type*} [Fintype Ω] [Fintype I] [Fintype H] [DecidableEq I]

noncomputable def inside (g a f : ℝ) (d : I → ℝ) (X : Ω → I → I → ℝ) (ω : Ω) : ℝ :=
  ∑ h, g*(d h-(∑ i, g*(1-X ω h i)*max (d h-a*d i) 0)-f)
noncomputable def external (g a B V : ℝ) (bH : H → ℝ) (d : I → ℝ)
    (X : Ω → H → I → ℝ) (ω : Ω) : ℝ :=
  ∑ h, g*(removedMass g X ω h*bH h-a*removedCost g d X ω h-
    B*removedMass g X ω h*(V-removedCost g d X ω h))

end MetricKMedian.GeneratorAverage
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_GroupCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.GroupCap
open Finset
variable {F E : Type*}

noncomputable def cap (R : ℝ) (d : F → ℝ) (O : Finset F) : ℝ := O.fold min (5*R) d

end MetricKMedian.GroupCap
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_FractionalListChecks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.LPBinary.Repair
open Function Finset

def bounded (q : ℚ) : Bool := decide (0 ≤ q ∧ q ≤ 1)
end MetricKMedian.LPBinary.Repair
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_InstanceParserProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.InputParser
open Finset
 theorem flatten_ofFn {n : ℕ} (d : Fin n → Fin n → ℚ) :
    (List.ofFn (fun i => List.ofFn (d i))).flatten=
      List.ofFn (fun k : Fin (n*n) => d (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) := by
  symm
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hij : i.val*n+j.val<n*n := by
    calc
      i.val*n+j.val < i.val*n+n := Nat.add_lt_add_left j.isLt _
      _ = (i.val+1)*n := by simp only [Nat.add_mul,Nat.one_mul]
      _ ≤ n*n := Nat.mul_le_mul_right n i.isLt
  have he : (⟨i.val*n+j.val, hij⟩ : Fin (n*n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext; change _=j.val+n*i.val; ac_rfl
  rw [he]
  exact congrArg (fun p : Fin n × Fin n => d p.1 p.2) (finProdFinEquiv.symm_apply_apply (i,j))
end MetricKMedian.InputParser
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
variable {n m : ℕ}

def stepHeight (n m N L : ℕ) :=
  let d := n*m+(n*m)*(n*m)
  L+((2*(d+1)*(d+1))*((d+1)*N+1))*((d+1)*N)

end MetricKMedian.SparseGraph
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

namespace MetricKMedian.SparseIntegerLaw
variable {α : Type} {d : ℕ}

def stepHeight (N d P F : ℕ) := P*N+(((2*(d+1)*(d+1+F*(2*N+1)))*(2*N+1))*(2*N))

end MetricKMedian.SparseIntegerLaw
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
variable {n d : ℕ}

def stepHeight (n d L : ℕ) := SparseIntegerLaw.stepHeight ((n+1)^d+1) ((n+1)^d) L 0

end MetricKMedian.SparseBernoulli
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliRunProgram
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
 theorem sizePolynomial_eval (d L : ℕ) : (sizePolynomial d).eval L=sizeBound d L := by
  simp only [sizePolynomial,sizeBound,heightBound,supportBound,HPoly,SPoly,SparseBernoulli.stepHeight,
    SparseIntegerLaw.stepHeight,eval_add,eval_mul,eval_ofNat,eval_X,eval_one,eval_pow,eval_zero]

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_BatchOrdinalCodes
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
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalBatchProgram
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
-- module Solutions.OAIQ053_KM.KMedian_Rounding_WeightedGridInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.RationalGrid

theorem add {D : ℤ} {a b : ℚ} (ha : At D a) (hb : At D b) : At D (a+b) := by
  obtain ⟨A,rfl⟩ := ha
  obtain ⟨B,rfl⟩ := hb
  exact ⟨A+B,by rw [Int.cast_add,add_div]⟩

theorem mul {D E : ℤ} {a b : ℚ} (ha : At D a) (hb : At E b) : At (D*E) (a*b) := by
  obtain ⟨A,rfl⟩ := ha
  obtain ⟨B,rfl⟩ := hb
  exact ⟨A*B,by rw [Int.cast_mul,Int.cast_mul,mul_div_mul_comm]⟩

end MetricKMedian.RationalGrid

end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingCoordinateHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.RationalGrid

theorem enlarge {D : ℤ} {q : ℚ} (hq : At D q) (E : ℤ) (hE : E≠0) : At (D*E) q := by
  simpa only [Int.cast_one,mul_one] using RationalGrid.mul hq (integer E 1 hE)

theorem divide_weight {D : ℤ} {β q : ℚ} (hD : D≠0) (hβ : β≠0) (hq : At D (β*q)) :
    At (D*β.num) q := by
  obtain ⟨A,ha⟩ := hq
  have hn : (β.num:ℚ)≠0 := by
    intro hz
    apply hβ
    rw [← Rat.num_div_den β,hz,zero_div]
  have hDc : (D:ℚ)≠0 := by exact_mod_cast hD
  refine ⟨A*β.den,?_⟩
  rw [Int.cast_mul,Int.cast_mul,Int.cast_natCast]
  apply (eq_div_iff (mul_ne_zero hDc hn)).mpr
  have hb := β.mul_den_eq_num
  calc
    q*((D:ℚ)*(β.num:ℚ)) = (β*q*(D:ℚ))*(β.den:ℚ) := by rw [← hb]; ring
    _ = (A:ℚ)*(β.den:ℚ) := by rw [(eq_div_iff hDc).mp ha]

end MetricKMedian.RationalGrid

end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingRunHeight
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
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingRunProgram
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
-- module Solutions.OAIQ053_KM.KMedian_Programs_GraphRunProgram
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


