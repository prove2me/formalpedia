-- Prove2me | Definitions.Def_OAIQ035K005
-- name    : OAIQ035K005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:53:34.312519+00:00
-- url     : https://prove2.me/theorems/93b874dd-ca17-4fc5-9218-b99a65b9fdc4
-- title:
--   Definitions bundle OAIQ035K005 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 48 declarations of OpenAI's Lean: 31 definitions, 3 inductive types or structures and 14 theorems. The definitions and types are `OAI.MetricKMedian.FiniteLaw.selected`, `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.Input`, `OAI.MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram.cap`, `OAI.MetricKMedian.FixedBatch.batchConstant`, `OAI.MetricKMedian.Gaussian.IsCircuit`, `OAI.MetricKMedian.Gaussian.RatMatrix`, `OAI.MetricKMedian.Gaussian.kernel`, `OAI.MetricKMedian.Gaussian.lift`, `OAI.MetricKMedian.Gaussian.residual`, `OAI.MetricKMedian.Gaussian.tabulate`, `OAI.MetricKMedian.Gaussian.values`, `OAI.MetricKMedian.IntegerLaw`, `OAI.MetricKMedian.IntegerLaw.ListPivot.Entry`, `OAI.MetricKMedian.IntegerLaw.activeMatrix`, `OAI.MetricKMedian.IntegerLaw.eliminateAt`, `OAI.MetricKMedian.IntegerLaw.positiveSet`, `OAI.MetricKMedian.IntegerLaw.ratio`, `OAI.MetricKMedian.IntegerLaw.rational`, `OAI.MetricKMedian.IntegerLaw.reindex`, `OAI.MetricKMedian.IntegerLaw.support`, `OAI.MetricKMedian.IntegerLaw.trim`, `OAI.MetricKMedian.MaskProgram.maximum`, `OAI.MetricKMedian.Preparation.RationalNearest.least`, `OAI.MetricKMedian.Preparation.RationalNearest.takeNearest`, `OAI.MetricKMedian.RationalBatchData.amount`, `OAI.MetricKMedian.RationalBatchData.bias`, `OAI.MetricKMedian.RationalBatchData.heavySet`, `OAI.MetricKMedian.RationalLaw`, `OAI.MetricKMedian.SparseBernoulli.endpoint`, `OAI.MetricKMedian.SparseBernoulli.features`, `OAI.MetricKMedian.SparseBernoulli.flag`, `OAI.MetricKMedian.SparseBernoulli.monomial`, `OAI.MetricKMedian.SparseBernoulli.used`, `OAI.MetricKMedian.SparseHistories.History`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Compression_AffineElimination`, `KMedian_Compression_AffineKernel`, `KMedian_Compression_ComputedAffineKernel`, `KMedian_Compression_ComputedPivot`, `KMedian_Compression_GaussianCircuit`, `KMedian_Compression_GaussianKernel`, `KMedian_Compression_GaussianTabulated`, `KMedian_Compression_RationalCompression`, `KMedian_Geometry_IntegerBranching`, `KMedian_Geometry_NearestReindex`, `KMedian_Geometry_RationalNearestCopies`, `KMedian_Geometry_TrimIntegerLaw`, `KMedian_Preparation_PreparedScanProgram`, `KMedian_Probability_BernoulliBatches`, `KMedian_Process_BatchUniform`, `KMedian_Process_RoundCountsProgram`, `KMedian_Programs_MaximumProgram`, `KMedian_Programs_PivotListProgram`, `KMedian_Rounding_RationalBatchData`, `KMedian_Rounding_RationalBatchFacts`, `KMedian_Sparse_SparseBernoulliFeatures`, `KMedian_Sparse_SparseHistories`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K016`, `OAIQ035K017`, `OAIQ035K018`, `OAIQ035K019`, `OAIQ035K020`, `OAIQ035K021`, `OAIQ035K022`, `OAIQ035K023`, `OAIQ035K024`, `OAIQ035K026`, `OAIQ035K038`, `OAIQ035K044` and `OAIQ035K062`; the statement `OAI_MetricKMedian_CopyState_assignment_copies`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_RationalCompression
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
-- module Solutions.OAIQ035_KM.KMedian_Compression_AffineElimination
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
-- module Solutions.OAIQ035_KM.KMedian_Compression_AffineKernel
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
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianKernel
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
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianCircuit
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
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianTabulated
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

end MetricKMedian.Gaussian

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_ComputedAffineKernel
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
-- module Solutions.OAIQ035_KM.KMedian_Compression_ComputedPivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

def positiveSet {n : ℕ} (z : Fin n → ℤ) : Finset (Fin n) :=
  univ.filter (fun i => 0 < z i)

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
-- module Solutions.OAIQ035_KM.KMedian_Geometry_IntegerBranching
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
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalNearestCopies
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
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliBatches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian
namespace FiniteLaw
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def selected (C : I → Finset I) (ω : I → Bool) : Finset I :=
  Finset.univ.filter (fun i => ω i = true ∧ ∀ j ∈ C i, ω j = false)

end FiniteLaw
end MetricKMedian

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
-- module Solutions.OAIQ035_KM.KMedian_Programs_PivotListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.IntegerLaw.ListPivot
open Function Finset
abbrev Entry := ℤ × ℤ

end MetricKMedian.IntegerLaw.ListPivot
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalBatchData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset
variable {I E : Type} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

def amount (m : I → ℚ) : ℚ := ∑ i, max (1-m i) 0

def bias (m : I → ℚ) (p φ : ℚ) (i : I) : ℚ := if 1< m i then (1+φ)*p else p

def heavySet (m : I → ℚ) (b : ℚ) : Finset I :=
  univ.filter (fun i => max 1 (b*amount m)< m i)

end MetricKMedian.RationalBatchData
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBernoulliFeatures
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
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalBatchFacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalBatchData
open Finset
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseHistories
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

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_NearestReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.Preparation.RationalNearest
open Finset
variable {α β : Type} [LinearOrder α] [LinearOrder β]
theorem min_map (e : α ≃o β) (U : Finset α) (hU : U.Nonempty) :
    (U.map e.toEmbedding).min' (hU.map) = e (U.min' hU) := by
  apply le_antisymm
  · exact min'_le _ _ (mem_map.mpr ⟨_,min'_mem U hU,rfl⟩)
  · obtain ⟨a,ha,he⟩ := mem_map.mp (min'_mem (U.map e.toEmbedding) (hU.map))
    rw [← he]
    exact e.monotone (min'_le U a ha)
 theorem least_map (e : α ≃o β) (U : Finset α) (d : α → ℚ) (hU : U.Nonempty) :
    least (U.map e.toEmbedding) (fun b => d (e.symm b)) (hU.map)=e (least U d hU) := by
  have him : (U.map e.toEmbedding).image (fun b => d (e.symm b))=U.image d := by
    ext q
    simp only [mem_image,mem_map]
    constructor
    · rintro ⟨b,⟨a,ha,rfl⟩,h⟩; exact ⟨a,ha,by simpa using h⟩
    · rintro ⟨a,ha,rfl⟩; exact ⟨e a,⟨a,ha,rfl⟩,by simp⟩
  unfold least
  have hf : (U.map e.toEmbedding).filter (fun b => d (e.symm b)=(U.image d).min' (hU.image _))=
      (U.filter (fun a => d a=(U.image d).min' (hU.image _))).map e.toEmbedding := by
    ext b
    simp only [mem_filter,mem_map]
    constructor
    · rintro ⟨⟨a,ha,rfl⟩,hh⟩; exact ⟨a,⟨ha,by simpa using hh⟩,rfl⟩
    · rintro ⟨a,⟨ha,hh⟩,rfl⟩; exact ⟨⟨a,ha,rfl⟩,by simpa using hh⟩
  simp only [him]
  simp only [hf]
  exact min_map e _ _

end MetricKMedian.Preparation.RationalNearest

end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_BatchUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset

noncomputable def batchConstant (Δ : ℕ) : ℝ :=
  let n : ℝ := Δ^2+Δ
  16*n*(Δ:ℝ)^2+256*n^2+16*n+6

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_MaximumProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.MaskProgram
open Finset
def maximum (xs : List ℚ) : ℚ := xs.foldl max (xs.head?.getD 0)
end MetricKMedian.MaskProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundCountsProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram
open Finset
variable {τ : ℝ}

def cap (Δ : ℕ) (ns : List ℕ) : Bool := (ns.map (fun n => decide (n≤Δ))).all id
end MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparedScanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram
open Finset
variable {τ : ℝ}
structure Input where
  f : ℕ
  h : ℕ
  j : ℕ
  df : Fin h → Fin h → ℚ
  dc : Fin j → Fin h → ℚ
  orig : Fin f → Fin h
  ns : List (Fin f → ℕ)
  budget : ℚ
end MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram
end

end OAI
end


