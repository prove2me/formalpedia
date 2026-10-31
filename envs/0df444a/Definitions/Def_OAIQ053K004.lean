-- Prove2me | Definitions.Def_OAIQ053K004
-- name    : OAIQ053K004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:53:43.972507+00:00
-- url     : https://prove2.me/theorems/197cfc4f-5eae-4448-948a-b24da34cfc04
-- title:
--   Definitions bundle OAIQ053K004 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 69 declarations of OpenAI's Lean: 44 definitions, 4 inductive types or structures, 2 instances and 19 theorems. The definitions and types are `OAI.MetricKMedian.Compression.extendVector`, `OAI.MetricKMedian.FiniteLaw`, `OAI.MetricKMedian.FiniteLaw.bind`, `OAI.MetricKMedian.FiniteLaw.dirac`, `OAI.MetricKMedian.FiniteLaw.expect`, `OAI.MetricKMedian.FiniteLaw.map`, `OAI.MetricKMedian.FixedBatch.Actions`, `OAI.MetricKMedian.FixedBatch.HeavyAction`, `OAI.MetricKMedian.FixedBatch.heavyParent`, `OAI.MetricKMedian.Gaussian.IsCircuit`, `OAI.MetricKMedian.Gaussian.ListOperation.Row`, `OAI.MetricKMedian.Gaussian.RatMatrix`, `OAI.MetricKMedian.Gaussian.kernel`, `OAI.MetricKMedian.Gaussian.kernelVector`, `OAI.MetricKMedian.Gaussian.lift`, `OAI.MetricKMedian.Gaussian.residual`, `OAI.MetricKMedian.Gaussian.tabulate`, `OAI.MetricKMedian.Gaussian.values`, `OAI.MetricKMedian.IntegerLaw`, `OAI.MetricKMedian.IntegerLaw.activeMatrix`, `OAI.MetricKMedian.IntegerLaw.eliminateAt`, `OAI.MetricKMedian.IntegerLaw.ratio`, `OAI.MetricKMedian.IntegerLaw.rational`, `OAI.MetricKMedian.IntegerLaw.reindex`, `OAI.MetricKMedian.IntegerLaw.support`, `OAI.MetricKMedian.IntegerLaw.trim`, `OAI.MetricKMedian.Preparation.RationalNearest.least`, `OAI.MetricKMedian.Preparation.RationalNearest.takeNearest`, `OAI.MetricKMedian.Preparation.nearFactor`, `OAI.MetricKMedian.Preparation.shortfallFactor`, `OAI.MetricKMedian.RationalBatchData.Event`, `OAI.MetricKMedian.RationalBatchData.amount`, `OAI.MetricKMedian.RationalBatchData.balanced`, `OAI.MetricKMedian.RationalBatchData.bias`, `OAI.MetricKMedian.RationalBatchData.conflicts`, `OAI.MetricKMedian.RationalBatchData.enumeration`, `OAI.MetricKMedian.RationalBatchData.graph`, `OAI.MetricKMedian.RationalBatchData.graphMass`, `OAI.MetricKMedian.RationalBatchData.heavy`, `OAI.MetricKMedian.RationalBatchData.heavySet` and 8 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Compression_AffineElimination`, `KMedian_Compression_AffineKernel`, `KMedian_Compression_ComputedAffineKernel`, `KMedian_Compression_ComputedPivot`, `KMedian_Compression_FinsetVectorExtension`, `KMedian_Compression_GaussianCircuit`, `KMedian_Compression_GaussianKernel`, `KMedian_Compression_GaussianListOperations`, `KMedian_Compression_GaussianTabulated`, `KMedian_Compression_GramBounds`, `KMedian_Compression_IntegerCoefficientBounds`, `KMedian_Compression_RationalCompression`, `KMedian_Geometry_FixedBatchTransition`, `KMedian_Geometry_IntegerBranching`, `KMedian_Geometry_RationalNearestCopies`, `KMedian_Geometry_TrimIntegerLaw`, `KMedian_Preparation_PreparationParameters`, `KMedian_Probability_FiniteKernels`, `KMedian_Probability_FiniteLawConstructions`, `KMedian_Probability_FiniteLaws`, `KMedian_Process_HeavyActions`, `KMedian_Rounding_RationalBatchData`, `KMedian_Rounding_RationalBatchEnumeration`, `KMedian_Rounding_RationalBatchFacts`, `KMedian_Rounding_RationalRoundEvents`, `KMedian_Sparse_SparseBernoulliFeatures`, `KMedian_Sparse_SparseGraphFeatures`, `KMedian_Sparse_SparseHistories`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K015`, `OAIQ053K016`, `OAIQ053K017`, `OAIQ053K018`, `OAIQ053K019`, `OAIQ053K020` and `OAIQ053K027`; the statement `OAI.MetricKMedian.GeneratorAverage.averaged_ideal_drift_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_RationalCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian
open Finset

structure RationalLaw (Ω : Type) [Fintype Ω] where
  weight : Ω → ℚ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω=1

end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_AffineElimination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian
open Finset

structure IntegerLaw (Ω : Type) [Fintype Ω] where
  denominator : ℤ
  denominator_pos : 0 < denominator
  numerator : Ω → ℤ
  numerator_nonneg : ∀ i, 0 ≤ numerator i
  total : ∑ i, numerator i=denominator

namespace IntegerLaw
variable {Ω I : Type} [Fintype Ω] [Fintype I]

def rational (μ : IntegerLaw Ω) : RationalLaw Ω where
  weight i := (μ.numerator i:ℚ)/μ.denominator
  nonneg i := div_nonneg (by exact_mod_cast μ.numerator_nonneg i)
    (by exact_mod_cast μ.denominator_pos.le)
  total := by rw [← sum_div,← Int.cast_sum,μ.total]; exact div_self (by exact_mod_cast μ.denominator_pos.ne')

end IntegerLaw
end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GramBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Compression
open Finset Matrix
variable {R C : Type} [Fintype R] [Fintype C] [DecidableEq C]

omit [Fintype C] [DecidableEq C] in
                                                                      
theorem gram_entry_bound (A : Matrix R C ℤ) (M : ℤ) (hM : 0 ≤ M)
    (hA : ∀ r c, |A r c| ≤ M) (c d : C) :
    |(A.transpose*A) c d| ≤ (Fintype.card R:ℤ)*M^2 := by
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ r, |A r c*A r d| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : R, M^2 := sum_le_sum (fun r _ => by
      rw [abs_mul,pow_two]
      exact mul_le_mul (hA r c) (hA r d) (abs_nonneg _) hM)
    _ = _ := by simp

omit [Fintype C] [DecidableEq C] in
theorem gram_rhs_bound (A : Matrix R C ℤ) (w : R → ℤ) (M : ℤ) (hM : 0 ≤ M)
    (hA : ∀ r c, |A r c| ≤ M) (hw : ∀ r, |w r| ≤ M) (c : C) :
    |(A.transpose*ᵥw) c| ≤ (Fintype.card R:ℤ)*M^2 := by
  change |∑ r, A r c*w r| ≤ _
  calc
    _ ≤ ∑ r, |A r c*w r| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : R, M^2 := sum_le_sum (fun r _ => by
      rw [abs_mul,pow_two]
      exact mul_le_mul (hA r c) (hw r) (abs_nonneg _) hM)
    _ = _ := by simp

theorem gram_det_bound (A : Matrix R C ℤ) (M : ℤ) (hM : 0 ≤ M)
    (hA : ∀ r c, |A r c| ≤ M) :
    |(A.transpose*A).det| ≤ (Nat.factorial (Fintype.card C):ℤ)*
      ((Fintype.card R:ℤ)*M^2)^(Fintype.card C) := by
  simpa only [AbsoluteValue.abs_apply,nsmul_eq_mul] using
    (Matrix.det_le (abv := AbsoluteValue.abs) (gram_entry_bound A M hM hA))

end MetricKMedian.Compression

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_IntegerCoefficientBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Compression

theorem gram_coefficient_bit_bound (r n L : ℕ) (hn : n ≤ r) :
    (n.factorial:ℤ)*((r:ℤ)*((2:ℤ)^L)^2)^n ≤ (2:ℤ)^(2*r*(r+L)) := by
  have hnr : n ≤ 2^r := hn.trans Nat.lt_two_pow_self.le
  have hf : n.factorial ≤ 2^(r*r) := by
    calc
      _ ≤ n^n := Nat.factorial_le_pow n
      _ ≤ (2^r)^n := Nat.pow_le_pow_left hnr n
      _ = 2^(r*n) := (pow_mul _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left r hn)
  have hfZ : (n.factorial:ℤ) ≤ 2^(r*r) := by exact_mod_cast hf
  have hrZ : (r:ℤ) ≤ 2^r := by exact_mod_cast (Nat.lt_two_pow_self (n:=r)).le
  have hb : (r:ℤ)*((2:ℤ)^L)^2 ≤ 2^(r+2*L) := by
    calc
      _ ≤ 2^r*((2:ℤ)^L)^2 := mul_le_mul_of_nonneg_right hrZ (sq_nonneg _)
      _ = _ := by rw [pow_add,Nat.mul_comm 2 L,pow_mul]
  have hbn : ((r:ℤ)*((2:ℤ)^L)^2)^n ≤ 2^((r+2*L)*r) := by
    calc
      _ ≤ ((2:ℤ)^(r+2*L))^n := pow_le_pow_left₀ (by positivity) hb n
      _ = 2^((r+2*L)*n) := (pow_mul _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hn)
  calc
    _ ≤ 2^(r*r)*(2:ℤ)^((r+2*L)*r) :=
      mul_le_mul hfZ hbn (by positivity) (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; ring

end MetricKMedian.Compression

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_AffineKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset
variable {Ω I : Type} [Fintype Ω] [Fintype I]

def support (μ : IntegerLaw Ω) : Finset Ω :=
  univ.filter (fun i => μ.numerator i ≠ 0)

@[simp] theorem mem_support (μ : IntegerLaw Ω) (i : Ω) :
    i ∈ μ.support ↔ μ.numerator i ≠ 0 := by simp [support]

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Gaussian
open Finset

def residual {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ) (p : Fin (n+1)) :
    Fin r → Fin n → ℚ :=
  fun i j => A i.succ (p.succAbove j) - A 0 (p.succAbove j)/A 0 p*A i.succ p

def lift {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ) (p : Fin (n+1))
    (z : Fin n → ℚ) : Fin (n+1) → ℚ :=
  p.insertNth (-(∑ j, A 0 (p.succAbove j)/A 0 p*z j)) z

def kernel : (r n : ℕ) → (Fin r → Fin n → ℚ) → Fin n → ℚ
  | 0, _, _ => fun j => if j.val=0 then 1 else 0
  | _+1, 0, _ => Fin.elim0
  | r+1, n+1, A =>
    if h : (univ.filter (fun j => A 0 j ≠ 0)).Nonempty then
      let p := (univ.filter (fun j => A 0 j ≠ 0)).min' h
      lift A p (kernel r n (residual A p))
    else kernel r (n+1) (fun i j => A i.succ j)

end MetricKMedian.Gaussian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Gaussian
open Finset

def IsCircuit {r n : ℕ} (A : Fin r → Fin n → ℚ) (z : Fin n → ℚ) : Prop :=
  ∀ v : Fin n → ℚ, (∀ j, z j=0 → v j=0) → (∀ i, ∑ j, A i j*v j=0) →
    ∃ t : ℚ, ∀ j, v j=t*z j

end MetricKMedian.Gaussian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianTabulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Gaussian
open Finset

abbrev RatMatrix (r n : ℕ) := Vector (Vector ℚ n) r

def values {r n : ℕ} (A : RatMatrix r n) (i : Fin r) (j : Fin n) : ℚ :=
  A[i.val][j.val]

def tabulate {r n : ℕ} (A : Fin r → Fin n → ℚ) : RatMatrix r n :=
  Vector.ofFn (fun i => Vector.ofFn (A i))

@[simp] theorem values_tabulate {r n : ℕ} (A : Fin r → Fin n → ℚ) :
    values (tabulate A)=A := by
  funext i j
  simp only [values,tabulate,Vector.getElem_ofFn]

def kernelVector : (r n : ℕ) → RatMatrix r n → Vector ℚ n
  | 0, _, _ => Vector.ofFn (fun j => if j.val=0 then 1 else 0)
  | _+1, 0, _ => Vector.ofFn Fin.elim0
  | r+1, n+1, A =>
    let a := values A
    if h : (univ.filter (fun j => a 0 j ≠ 0)).Nonempty then
      let p := (univ.filter (fun j => a 0 j ≠ 0)).min' h
      let B := tabulate (residual a p)
      let z := kernelVector r n B
      Vector.ofFn (lift a p (fun j => z[j.val]))
    else kernelVector r (n+1) (tabulate (fun i j => a i.succ j))

end MetricKMedian.Gaussian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_FinsetVectorExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Compression
open Finset

def extendVector {n : ℕ} (s : Finset (Fin n)) (z : Fin s.card → ℤ) (i : Fin n) : ℤ :=
  if h : i ∈ s then z ((s.orderIsoOfFin rfl).symm ⟨i,h⟩) else 0

end MetricKMedian.Compression

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_ComputedAffineKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

def activeMatrix {n d : ℕ} (μ : IntegerLaw (Fin n)) (v : Fin n → Fin d → ℤ) :
    Fin (d+1) → Fin μ.support.card → ℤ :=
  fun j i => Fin.cases 1 (fun j => v ((μ.support.orderIsoOfFin rfl) i).val j) j

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_ComputedPivot
attribute [-simp] _root_.OAI.MetricKMedian.IntegerLaw.mem_support
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

def ratio {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ) (i : Fin n) : ℚ :=
  (μ.numerator i:ℚ)/(z i:ℚ)

theorem updated_nonneg {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ)
    (p : Fin n) (hp : 0 < z p)
    (hmin : ∀ i, 0 < z i → ratio μ z p ≤ ratio μ z i) (i : Fin n) :
    0 ≤ μ.numerator i*z p-μ.numerator p*z i := by
  by_cases hzi : 0 < z i
  · have hqp : (0:ℚ) < z p := by exact_mod_cast hp
    have hqi : (0:ℚ) < z i := by exact_mod_cast hzi
    have hh := (div_le_div_iff₀ hqp hqi).mp (hmin i hzi)
    have hhZ : μ.numerator p*z i ≤ μ.numerator i*z p := by exact_mod_cast hh
    exact sub_nonneg.mpr hhZ
  · have hle : z i ≤ 0 := le_of_not_gt hzi
    exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos (μ.numerator_nonneg p) hle).trans
      (mul_nonneg (μ.numerator_nonneg i) hp.le))

def eliminateAt {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ) (p : Fin n)
    (hp : 0 < z p) (hmin : ∀ i, 0 < z i → ratio μ z p ≤ ratio μ z i)
    (hzsum : ∑ i, z i=0) : IntegerLaw (Fin n) :=
  let b := Vector.ofFn (fun i => μ.numerator i*z p-μ.numerator p*z i)
  { denominator := μ.denominator*z p
    denominator_pos := mul_pos μ.denominator_pos hp
    numerator := fun i => b[i.val]
    numerator_nonneg := by
      intro i
      simp only [b,Vector.getElem_ofFn]
      exact updated_nonneg μ z p hp hmin i
    total := by
      simp only [b,Vector.getElem_ofFn,sum_sub_distrib,← sum_mul,← mul_sum,
        μ.total,hzsum,mul_zero,sub_zero] }

@[simp] theorem eliminateAt_numerator {n : ℕ} (μ : IntegerLaw (Fin n))
    (z : Fin n → ℤ) (p : Fin n) (hp : 0 < z p)
    (hmin : ∀ i, 0 < z i → ratio μ z p ≤ ratio μ z i) (hzsum : ∑ i, z i=0)
    (i : Fin n) : (eliminateAt μ z p hp hmin hzsum).numerator i=
      μ.numerator i*z p-μ.numerator p*z i := by
  simp only [eliminateAt,Vector.getElem_ofFn]

end MetricKMedian.IntegerLaw

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

abbrev Row := List ℚ
end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_FixedBatchTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset

variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

structure Actions (I E : Type*) [DecidableEq I] [DecidableEq E] where
  source : E → I
  erase : E → Finset I
  ordinary : Finset E

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_IntegerBranching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset
variable {α β : Type} [Fintype α] [Fintype β]

def reindex (μ : IntegerLaw α) (e : α ≃ β) : IntegerLaw β where
  denominator := μ.denominator
  denominator_pos := μ.denominator_pos
  numerator := fun b => μ.numerator (e.symm b)
  numerator_nonneg _b := μ.numerator_nonneg _
  total := (e.symm.sum_comp _).trans μ.total

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalNearestCopies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.RationalNearest
open Finset
variable {α : Type} [LinearOrder α]

def least (U : Finset α) (d : α → ℚ) (hU : U.Nonempty) : α :=
  let m := (U.image d).min' (hU.image _)
  let V := U.filter (fun a => d a=m)
  have hV : V.Nonempty := by
    obtain ⟨a,ha,he⟩ := mem_image.mp (min'_mem (U.image d) (hU.image _))
    exact ⟨a,mem_filter.mpr ⟨ha,he⟩⟩
  V.min' hV

theorem least_spec (U : Finset α) (d : α → ℚ) (hU : U.Nonempty) :
    least U d hU ∈ U ∧ ∀ a∈U, d (least U d hU) ≤ d a := by
  let V := U.filter (fun a => d a=(U.image d).min' (hU.image _))
  have hV : V.Nonempty := by
    obtain ⟨a,ha,he⟩ := mem_image.mp (min'_mem (U.image d) (hU.image _))
    exact ⟨a,mem_filter.mpr ⟨ha,he⟩⟩
  change V.min' hV ∈ U ∧ ∀ a∈U, d (V.min' hV) ≤ d a
  have hh := mem_filter.mp (min'_mem V hV)
  refine ⟨hh.1,fun a ha => ?_⟩
  rw [hh.2]
  exact min'_le _ _ (mem_image.mpr ⟨a,ha,rfl⟩)

def takeNearest (d : α → ℚ) : ℕ → Finset α → Finset α
  | 0,_ => ∅
  | k+1,U => if hU : U.Nonempty then
      insert (least U d hU) (takeNearest d k (U.erase (least U d hU))) else ∅

end MetricKMedian.Preparation.RationalNearest
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_TrimIntegerLaw
attribute [-simp] _root_.OAI.MetricKMedian.IntegerLaw.eliminateAt_numerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

def trim {n : ℕ} (μ : IntegerLaw (Fin n)) : IntegerLaw (Fin μ.support.card) where
  denominator := μ.denominator
  denominator_pos := μ.denominator_pos
  numerator := let v := Vector.ofFn (fun i => μ.numerator (μ.support.orderEmbOfFin rfl i))
    fun i => v[i.val]
  numerator_nonneg i := by
    simpa only [Vector.getElem_ofFn] using
      μ.numerator_nonneg (μ.support.orderEmbOfFin rfl i)
  total := by
    simp only [Vector.getElem_ofFn]
    calc
      _ = ∑ i : μ.support, μ.numerator i :=
        Equiv.sum_comp (μ.support.orderIsoOfFin rfl).toEquiv _
      _ = ∑ i ∈ μ.support, μ.numerator i := sum_coe_sort μ.support μ.numerator
      _ = ∑ i, μ.numerator i := by
        apply sum_subset (subset_univ _)
        intro i _ hi
        exact not_not.mp (by simpa only [mem_support] using hi)
      _ = _ := μ.total

@[simp] theorem trim_denominator {n : ℕ} (μ : IntegerLaw (Fin n)) :
    μ.trim.denominator=μ.denominator := rfl

@[simp] theorem trim_numerator {n : ℕ} (μ : IntegerLaw (Fin n))
    (i : Fin μ.support.card) :
    μ.trim.numerator i=μ.numerator (μ.support.orderEmbOfFin rfl i) := by
  simp only [trim,Vector.getElem_ofFn]

@[simp] theorem trim_weight {n : ℕ} (μ : IntegerLaw (Fin n))
    (i : Fin μ.support.card) :
    μ.trim.rational.weight i=μ.rational.weight (μ.support.orderEmbOfFin rfl i) := by
  simp only [rational,trim_numerator,trim_denominator]

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparationParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation

noncomputable def shortfallFactor (p₀ γ g : ℝ) : ℝ :=
  Real.sqrt g+Real.sqrt (g/p₀)+(γ+Real.sqrt (g*(1+γ)))/p₀
noncomputable def nearFactor (p₀ Q γ g : ℝ) : ℝ :=
  1/p₀+Q*shortfallFactor p₀ γ g

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_FiniteLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]
noncomputable def expect (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ := ∑ ω, μ.weight ω * f ω

end FiniteLaw

end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_FiniteLawConstructions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.FiniteLaw

noncomputable def dirac {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (ω₀ : Ω) : FiniteLaw Ω where
  weight ω := if ω=ω₀ then 1 else 0
  nonneg ω := by split_ifs <;> norm_num
  total := by simp

theorem expect_dirac {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (ω₀ : Ω) (f : Ω → ℝ) :
    (dirac ω₀).expect f = f ω₀ := by simp [expect, dirac]

end MetricKMedian.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_FiniteKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.FiniteLaw

variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

noncomputable def bind (μ : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ) : FiniteLaw Ξ where
  weight ξ := ∑ ω, μ.weight ω*(κ ω).weight ξ
  nonneg ξ := Finset.sum_nonneg (fun ω _ => mul_nonneg (μ.nonneg ω) ((κ ω).nonneg ξ))
  total := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, FiniteLaw.total, mul_one]

theorem expect_bind (μ : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ) (f : Ξ → ℝ) :
    (μ.bind κ).expect f = μ.expect (fun ω => (κ ω).expect f) := by
  simp only [bind, expect, Finset.sum_mul, mul_assoc, Finset.mul_sum]
  exact Finset.sum_comm

noncomputable def map [DecidableEq Ξ] (μ : FiniteLaw Ω) (f : Ω → Ξ) : FiniteLaw Ξ :=
  μ.bind (fun ω => dirac (f ω))

theorem expect_map [DecidableEq Ξ] (μ : FiniteLaw Ω) (f : Ω → Ξ) (g : Ξ → ℝ) :
    (μ.map f).expect g=μ.expect (fun ω => g (f ω)) := by
  rw [map, expect_bind]
  simp_rw [expect_dirac]

end MetricKMedian.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_HeavyActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset
variable {I : Type*} [DecidableEq I] [Fintype I]

abbrev HeavyAction (Full : Actions I I) (H : Finset I) :=
  {h : I // h ∉ H} ⊕ {p : I × I // p.1 ∈ H ∧ p.2 ∈ Full.erase p.1}

instance instFintypeHeavyAction (Full : Actions I I) (H : Finset I) : Fintype (HeavyAction Full H) := by
  unfold HeavyAction
  infer_instance

instance instDecidableEqHeavyAction (Full : Actions I I) (H : Finset I) : DecidableEq (HeavyAction Full H) := by
  unfold HeavyAction
  infer_instance

def heavyParent (Full : Actions I I) (H : Finset I) : HeavyAction Full H → I
  | .inl h => h
  | .inr p => p.val.1

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalBatchData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch
variable {I E : Type} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

def graph (G : I → Finset I) : Actions I I where
  source := id
  erase := fun h => univ.filter (fun i => h ∈ G i)
  ordinary := univ

def heavy (Full : Actions I I) (H : Finset I) : Actions I (HeavyAction Full H) where
  source := fun e => Full.source (heavyParent Full H e)
  erase := Sum.elim (fun h => Full.erase h) (fun p => {p.val.2})
  ordinary := univ.filter (fun e : HeavyAction Full H => e.isLeft = true)

def balanced (D : Actions I E) (Δ : ℕ) : Finset E :=
  D.ordinary.filter (fun e => (D.erase e).card=Δ)

def conflicts (D : Actions I E) (Δ : ℕ) (e : E) : Finset E :=
  if e ∈ balanced D Δ then
    (balanced D Δ).filter (fun f => f≠e ∧ (D.erase e ∩ D.erase f).Nonempty) else ∅

def amount (m : I → ℚ) : ℚ := ∑ i, max (1-m i) 0

def bias (m : I → ℚ) (p φ : ℚ) (i : I) : ℚ := if 1< m i then (1+φ)*p else p

def heavySet (m : I → ℚ) (b : ℚ) : Finset I :=
  univ.filter (fun i => max 1 (b*amount m)< m i)

def graphMass (G : I → Finset I) (g : ℚ) (h : I) : ℚ := g*((graph G).erase h).card

end MetricKMedian.RationalBatchData
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalBatchEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch
variable {I : Type} [LinearOrder I] [Fintype I]

def enumeration (Full : Actions I I) (H : Finset I) :
    Fin (Fintype.card (HeavyAction Full H)) ≃ HeavyAction Full H := by
  letI : LinearOrder (I × I) :=
    LinearOrder.lift' (fun p : I × I => toLex p) (fun _ _ h => h)
  letI : LinearOrder (HeavyAction Full H) :=
    LinearOrder.lift' (fun e : HeavyAction Full H => toLex e) (fun _ _ h => h)
  exact (Fintype.orderIsoFinOfCardEq (HeavyAction Full H) rfl).toEquiv

end MetricKMedian.RationalBatchData
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBernoulliFeatures
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

def used (f : Fin d → Fin (n+1)) : Finset (Fin n) :=
  univ.filter (fun i => ∃ a : Fin d, (f a).val=i.val)

def flag (q : Fin n → Bool) (i : Fin n) : ℚ := if q i then 1 else 0

def monomial (q : Fin n → Bool) (f : Fin d → Fin (n+1)) : ℚ :=
  ∏ i ∈ used f, flag q i

def features (q : Fin n → Bool) (j : Fin ((n+1)^d)) : ℚ :=
  monomial q (finFunctionFinEquiv.symm j)

@[simp] theorem features_code (q : Fin n → Bool) (f : Fin d → Fin (n+1)) :
    features q (finFunctionFinEquiv f)=monomial q f := by
  simp only [features,Equiv.symm_apply_apply]

def endpoint (q : Fin n → Bool) (i : Fin n) (b : Fin 2) : Fin n → Bool :=
  fun x => if x=i then decide (b=0) else q x

@[simp] theorem flag_endpoint (q : Fin n → Bool) (i x : Fin n) (b : Fin 2) :
    flag (endpoint q i b) x=if x=i then (if b=0 then 1 else 0) else flag q x := by
  by_cases h : x=i <;> simp [flag,endpoint,h]

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalBatchFacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch
variable {I E : Type} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

omit [DecidableEq I] [Fintype I] in
theorem bias_bounds (m : I → ℚ) {p φ : ℚ} (hp : 0 ≤ p) (hφ : 0 ≤ φ) (i : I) :
    p ≤ bias m p φ i ∧ bias m p φ i ≤ (1+φ)*p := by
  unfold bias
  split_ifs <;> constructor <;> nlinarith only [mul_nonneg hp hφ]

omit [DecidableEq I] [Fintype I] in
theorem bias_probability (m : I → ℚ) {p φ : ℚ} (hp : 0 ≤ p) (hφ : 0 ≤ φ)
    (hupper : (1+φ)*p ≤ 1) (i : I) : 0 ≤ bias m p φ i ∧ bias m p φ i ≤ 1 :=
  ⟨hp.trans (bias_bounds m hp hφ i).1,(bias_bounds m hp hφ i).2.trans hupper⟩

end MetricKMedian.RationalBatchData
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalRoundEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset FixedBatch
variable {I : Type} [LinearOrder I] [Fintype I]

abbrev Event (I : Type) [DecidableEq I] [Fintype I] (g β : ℚ) :=
  (G : I → Finset I) × Finset (HeavyAction (graph G) (heavySet (graphMass G g) β))

end MetricKMedian.RationalBatchData
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseGraphFeatures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseGraph
open Finset
variable {n m : ℕ}

abbrev Graph (n m : ℕ) := Fin m → Finset (Fin n)

end MetricKMedian.SparseGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseHistories
open Finset
variable {α : Type}

abbrev History (α : Type) := α × List α

end MetricKMedian.SparseHistories
end
end

end OAI
end


