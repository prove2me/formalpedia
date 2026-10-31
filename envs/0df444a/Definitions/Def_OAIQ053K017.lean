-- Prove2me | Definitions.Def_OAIQ053K017
-- name    : OAIQ053K017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:56:11.987206+00:00
-- url     : https://prove2.me/theorems/54b791d7-f85f-43a0-99e5-9042d72cc75e
-- title:
--   Definitions bundle OAIQ053K017 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 60 declarations of OpenAI's Lean: 32 definitions and 28 theorems. The definitions and types are `OAI.MetricKMedian.CopyState.next`, `OAI.MetricKMedian.IntegerLaw.computedPivot`, `OAI.MetricKMedian.IntegerLaw.leastRatio`, `OAI.MetricKMedian.IntegerLaw.pivotSet`, `OAI.MetricKMedian.Preparation.RationalBundles.next`, `OAI.MetricKMedian.Preparation.RationalSuppliers.D`, `OAI.MetricKMedian.Preparation.RationalSuppliers.a`, `OAI.MetricKMedian.Preparation.RationalSuppliers.index`, `OAI.MetricKMedian.Preparation.RationalSuppliers.q`, `OAI.MetricKMedian.Preparation.RationalUnitInput.V`, `OAI.MetricKMedian.RationalBatchData.erased`, `OAI.MetricKMedian.RationalBatchData.opened`, `OAI.MetricKMedian.RationalBatchData.sources`, `OAI.MetricKMedian.RationalBatchData.transition`, `OAI.MetricKMedian.RationalLaw.scaledFeatures`, `OAI.MetricKMedian.RationalPhysicalKernel.own`, `OAI.MetricKMedian.RationalSignedTerminal.state`, `OAI.MetricKMedian.SparseBernoulli.target`, `OAI.MetricKMedian.SparseEnumeratedGraph.lift`, `OAI.MetricKMedian.SparseGraph.edge`, `OAI.MetricKMedian.SparseGraph.edgeCode`, `OAI.MetricKMedian.SparseGraph.features`, `OAI.MetricKMedian.SparseGraph.next`, `OAI.MetricKMedian.SparseHistories.extend`, `OAI.MetricKMedian.SparsePrepared.Program.BaseRaw`, `OAI.MetricKMedian.Taper.A`, `OAI.MetricKMedian.Taper.B`, `OAI.MetricKMedian.Taper.candidates`, `OAI.MetricKMedian.Taper.inverseRadius`, `OAI.MetricKMedian.Taper.rationalMass`, `OAI.MetricKMedian.Taper.rootCandidates`, `OAI.MetricKMedian.Taper.sourceMarginals`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Compression_ComputedPivot`, `KMedian_Compression_GaussianCircuit`, `KMedian_Compression_GaussianKernel`, `KMedian_Compression_GaussianTabulated`, `KMedian_Compression_RationalScaling`, `KMedian_Geometry_ComputedRationalCompression`, `KMedian_Geometry_RationalBundleGeometry`, `KMedian_Geometry_RationalUnitInput`, `KMedian_Preparation_PreparedDataOperations`, `KMedian_Preparation_RationalSupplierPreparation`, `KMedian_Process_CopyState`, `KMedian_Rounding_RationalCopyTransition`, `KMedian_Rounding_RationalPhysicalKernel`, `KMedian_Rounding_RationalSignedStep`, `KMedian_Rounding_RationalSignedTerminal`, `KMedian_Rounding_RationalTaper`, `KMedian_Rounding_RationalTaperAffine`, `KMedian_Rounding_RationalTaperCandidates`, `KMedian_Rounding_RationalTaperData`, `KMedian_Rounding_WeightedRounding`, `KMedian_Sparse_SparseBernoulliFeatures`, `KMedian_Sparse_SparseEnumeratedGraph`, `KMedian_Sparse_SparseGraphFeatures`, `KMedian_Sparse_SparseHistories`.
--
--   **Imports.** It imports the bundles `OAIQ053K000`, `OAIQ053K001`, `OAIQ053K002`, `OAIQ053K003`, `OAIQ053K004` and `OAIQ053K005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K030`, `OAIQ053K031`, `OAIQ053K032`, `OAIQ053K033`, `OAIQ053K034`, `OAIQ053K036` and `OAIQ053K037`; the statements `OAI.MetricKMedian.CopyState.balanced_count_change_s53`, `OAI.MetricKMedian.CopyState.unbalanced_count_change_s53` and `OAI.MetricKMedian.CopyState.unbalanced_small_change_s53`; the proofs of `OAI.MetricKMedian.CopyState.balanced_count_change_s53`, `OAI.MetricKMedian.CopyState.unbalanced_count_change_s53` and `OAI.MetricKMedian.CopyState.unbalanced_small_change_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K000
import Definitions.Def_OAIQ053K001
import Definitions.Def_OAIQ053K002
import Definitions.Def_OAIQ053K003
import Definitions.Def_OAIQ053K004
import Definitions.Def_OAIQ053K005

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_ComputedPivot
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

def leastRatio {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ)
    (h : (positiveSet z).Nonempty) : ℚ :=
  ((positiveSet z).image (ratio μ z)).min' (h.image _)

def pivotSet {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ)
    (h : (positiveSet z).Nonempty) : Finset (Fin n) :=
  (positiveSet z).filter (fun i => ratio μ z i=leastRatio μ z h)

theorem pivotSet_nonempty {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ)
    (h : (positiveSet z).Nonempty) : (pivotSet μ z h).Nonempty := by
  obtain ⟨i,hi,he⟩ := mem_image.mp
    (min'_mem ((positiveSet z).image (ratio μ z)) (h.image _))
  exact ⟨i,mem_filter.mpr ⟨hi,he⟩⟩

def computedPivot {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ)
    (h : (positiveSet z).Nonempty) : Fin n :=
  (pivotSet μ z h).min' (pivotSet_nonempty μ z h)

theorem computedPivot_spec {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ)
    (h : (positiveSet z).Nonempty) :
    0 < z (computedPivot μ z h) ∧
      ∀ i, 0 < z i → ratio μ z (computedPivot μ z h) ≤ ratio μ z i := by
  have hp := mem_filter.mp (min'_mem (pivotSet μ z h) (pivotSet_nonempty μ z h))
  refine ⟨(mem_filter.mp hp.1).2,?_⟩
  intro i hi
  rw [computedPivot,hp.2]
  exact min'_le _ _ (mem_image_of_mem (ratio μ z)
    (mem_filter.mpr ⟨mem_univ _,hi⟩))

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianKernel
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Gaussian
open Finset

theorem lift_kernel {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ) (p : Fin (n+1))
    (hp : A 0 p ≠ 0) (z : Fin n → ℚ)
    (hz : ∀ i, ∑ j, residual A p i j*z j=0) :
    ∀ i, ∑ j, A i j*lift A p z j=0 := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [Fin.sum_univ_succAbove _ p]
    simp only [lift,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,mul_neg]
    have hs : A 0 p*(∑ j, A 0 (p.succAbove j)/A 0 p*z j)=
        ∑ j, A 0 (p.succAbove j)*z j := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      field_simp
    rw [hs,neg_add_cancel]
  · rw [Fin.sum_univ_succAbove _ p]
    simp only [lift,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
    have hh := hz i
    simp only [residual,sub_mul,sum_sub_distrib] at hh
    have he : (∑ j, A 0 (p.succAbove j)/A 0 p*A i.succ p*z j)=
        A i.succ p*(∑ j, A 0 (p.succAbove j)/A 0 p*z j) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    rw [he] at hh
    linarith

end MetricKMedian.Gaussian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianCircuit
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Gaussian
open Finset

theorem lift_eq_of_kernel {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ)
    (p : Fin (n+1)) (hp : A 0 p ≠ 0) (v : Fin (n+1) → ℚ)
    (h0 : ∑ j, A 0 j*v j=0) :
    v=lift A p (fun j => v (p.succAbove j)) := by
  have he : v p= -(∑ j, A 0 (p.succAbove j)/A 0 p*v (p.succAbove j)) := by
    rw [Fin.sum_univ_succAbove _ p] at h0
    have hs : A 0 p*(∑ j, A 0 (p.succAbove j)/A 0 p*v (p.succAbove j))=
        ∑ j, A 0 (p.succAbove j)*v (p.succAbove j) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      field_simp
    apply (mul_left_cancel₀ hp)
    rw [mul_neg,hs]
    linarith
  funext j
  by_cases hj : j=p
  · subst j
    simpa only [lift,Fin.insertNth_apply_same] using he
  · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hj
    simp only [lift,Fin.insertNth_apply_succAbove]

theorem residual_kernel {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ)
    (p : Fin (n+1)) (hp : A 0 p ≠ 0) (v : Fin (n+1) → ℚ)
    (hv : ∀ i, ∑ j, A i j*v j=0) :
    ∀ i, ∑ j, residual A p i j*v (p.succAbove j)=0 := by
  have he := lift_eq_of_kernel A p hp v (hv 0)
  intro i
  have hi := hv i.succ
  rw [Fin.sum_univ_succAbove _ p] at hi
  have hep := congrFun he p
  simp only [lift,Fin.insertNth_apply_same] at hep
  rw [hep] at hi
  simp only [residual,sub_mul,sum_sub_distrib]
  have hs : (∑ j, A 0 (p.succAbove j)/A 0 p*A i.succ p*v (p.succAbove j))=
      A i.succ p*(∑ j, A 0 (p.succAbove j)/A 0 p*v (p.succAbove j)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    ring
  rw [hs]
  linarith

theorem lift_smul {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ)
    (p : Fin (n+1)) (z : Fin n → ℚ) (t : ℚ) :
    lift A p (fun j => t*z j)=fun j => t*lift A p z j := by
  funext j
  by_cases hj : j=p
  · subst j
    simp only [lift,Fin.insertNth_apply_same]
    rw [mul_neg, mul_sum]
    congr 1
    apply sum_congr rfl
    intro i _
    ring
  · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hj
    simp only [lift,Fin.insertNth_apply_succAbove]

theorem lift_circuit {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ)
    (p : Fin (n+1)) (hp : A 0 p ≠ 0) (z : Fin n → ℚ)
    (hz : IsCircuit (residual A p) z) : IsCircuit A (lift A p z) := by
  intro v hs hv
  have hsub : ∀ j, z j=0 → v (p.succAbove j)=0 := by
    intro j hj
    apply hs
    simpa only [lift,Fin.insertNth_apply_succAbove] using hj
  obtain ⟨t,ht⟩ := hz (fun j => v (p.succAbove j)) hsub (residual_kernel A p hp v hv)
  refine ⟨t,?_⟩
  have he := lift_eq_of_kernel A p hp v (hv 0)
  rw [show (fun j => v (p.succAbove j))=(fun j => t*z j) from funext ht,lift_smul] at he
  exact congrFun he

theorem kernel_circuit (r n : ℕ) (A : Fin r → Fin n → ℚ) (hn : r < n) :
    (∃ j, kernel r n A j=1) ∧ IsCircuit A (kernel r n A) := by
  induction r generalizing n with
  | zero =>
    let j0 : Fin n := ⟨0,hn⟩
    refine ⟨⟨j0,by simp only [kernel,j0,ite_true]⟩,?_⟩
    intro v hs _
    refine ⟨v j0,?_⟩
    intro j
    by_cases hj : j.val=0
    · have he : j=j0 := Fin.ext hj
      subst j
      simp only [kernel,j0,ite_true,mul_one]
    · have hh := hs j (by simp only [kernel,ite_eq_right hj])
      simp only [kernel,ite_eq_right hj,mul_zero,hh]
  | succ r ih =>
    cases n with
    | zero => omega
    | succ n =>
      by_cases hh : (univ.filter (fun j => A 0 j ≠ 0)).Nonempty
      · let p := (univ.filter (fun j => A 0 j ≠ 0)).min' hh
        have hp : A 0 p ≠ 0 := (mem_filter.mp (min'_mem _ hh)).2
        obtain ⟨⟨j,hj⟩,hc⟩ := ih n (residual A p) (by omega)
        have he : kernel (r+1) (n+1) A=lift A p (kernel r n (residual A p)) := by
          rw [kernel,dite_eq_left hh]
        rw [he]
        refine ⟨⟨p.succAbove j,?_⟩,lift_circuit A p hp _ hc⟩
        simpa only [lift,Fin.insertNth_apply_succAbove] using hj
      · have hi := ih (n+1) (fun i j => A i.succ j) (by omega)
        have he : kernel (r+1) (n+1) A=kernel r (n+1) (fun i j => A i.succ j) := by
          rw [kernel,dite_eq_right hh]
        rw [he]
        refine ⟨hi.1,?_⟩
        intro v hs hv
        exact hi.2 v hs (fun i => hv i.succ)

end MetricKMedian.Gaussian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianTabulated
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Gaussian
open Finset

theorem kernelVector_eq (r n : ℕ) (A : RatMatrix r n) :
    (fun j : Fin n => (kernelVector r n A)[j.val])=kernel r n (values A) := by
  induction r generalizing n with
  | zero => funext j; simp only [kernelVector,kernel,Vector.getElem_ofFn]
  | succ r ih =>
    cases n with
    | zero => exact funext (fun j => Fin.elim0 j)
    | succ n =>
      by_cases h : (univ.filter (fun j => values A 0 j ≠ 0)).Nonempty
      · rw [kernelVector,kernel,dite_eq_left h,dite_eq_left h]
        have hh := ih n (tabulate (residual (values A) ((univ.filter (fun j => values A 0 j ≠ 0)).min' h)))
        simp only [values_tabulate] at hh
        funext j
        simp only [Vector.getElem_ofFn]
        rw [hh]
      · rw [kernelVector,kernel,dite_eq_right h,dite_eq_right h]
        have hh := ih (n+1) (tabulate (fun i j => values A i.succ j))
        simpa only [values_tabulate] using hh

end MetricKMedian.Gaussian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_RationalScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.RationalScaling
open Finset
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

theorem numerator_bound (q : Ω → ℚ) (L : ℕ)
    (hqnum : ∀ i, |(q i).num| ≤ (2:ℤ)^L)
    (hqden : ∀ i, ((q i).den:ℤ) ≤ (2:ℤ)^L) (i : Ω) :
    |numerator q i| ≤ (2:ℤ)^(L*(Fintype.card Ω+1)) := by
  have hprod0 : 0 ≤ ∏ j ∈ univ.erase i, ((q j).den:ℤ) :=
    prod_nonneg (fun _ _ => by positivity)
  have hp : (∏ j ∈ univ.erase i, ((q j).den:ℤ)) ≤ (2:ℤ)^(L*Fintype.card Ω) := by
    calc
      _ ≤ ∏ _j ∈ univ.erase i, (2:ℤ)^L :=
        prod_le_prod (fun _ _ => by positivity) (fun index _ => hqden index)
      _ = (2:ℤ)^(L*(univ.erase i).card) := by rw [prod_const,pow_mul]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left L (card_erase_le.trans_eq (card_univ)))
  rw [numerator,abs_mul,abs_of_nonneg hprod0]
  calc
    _ ≤ (2:ℤ)^L * (2:ℤ)^(L*Fintype.card Ω) :=
      mul_le_mul (hqnum i) hp hprod0 (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; ring

end MetricKMedian.RationalScaling

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_ComputedRationalCompression
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.RationalLaw
open Finset

def scaledFeatures {n d : ℕ} (v : Fin n → Fin d → ℚ) : Fin n → Fin d → ℤ :=
  let M := Vector.ofFn (fun i => Vector.ofFn (fun j => RationalScaling.numerator (fun i => v i j) i))
  fun i j => M[i.val][j.val]

@[simp] theorem scaledFeatures_eq {n d : ℕ} (v : Fin n → Fin d → ℚ)
    (i : Fin n) (j : Fin d) :
    scaledFeatures v i j=RationalScaling.numerator (fun i => v i j) i := by
  simp only [scaledFeatures,Vector.getElem_ofFn]

end MetricKMedian.RationalLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalBundleGeometry
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.RationalBundles
open Finset
variable {n m : ℕ}

def next (d : Fin n → Fin n → ℚ) (t : Fin n) : Fin n :=
  if h : (univ.erase t).Nonempty then firstNearest (univ.erase t) (d t) h else t

end MetricKMedian.Preparation.RationalBundles
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

def V (c : Fin j) : ℚ := ∑ a ∈ U.F c, U.y a*U.dc c a

end RationalUnitInput
end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_WeightedRounding
attribute [-simp] _root_.OAI.MetricKMedian.RationalWeightedStep.real_down _root_.OAI.MetricKMedian.RationalWeightedStep.real_fractional _root_.OAI.MetricKMedian.RationalWeightedStep.real_move _root_.OAI.MetricKMedian.RationalWeightedStep.real_up
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.WeightedRounding

variable {I : Type*} [Fintype I] [DecidableEq I]
open MarginalRounding

omit [Fintype I] in
theorem move_left (p : I → ℝ) {i j : I} (hij : i ≠ j) (r t : ℝ) :
    move p i j r t i=p i+t := by simp only [move, sign, ite_true, ite_eq_right hij, sub_zero, mul_one]
omit [Fintype I] in
theorem move_right (p : I → ℝ) {i j : I} (hij : i ≠ j) (r t : ℝ) :
    move p i j r t j=p j-r*t := by simp only [move, sign, ite_eq_right hij.symm, ite_true, zero_sub]; ring
omit [Fintype I] in
theorem move_other (p : I → ℝ) {i j k : I} (hki : k ≠ i) (hkj : k ≠ j) (r t : ℝ) :
    move p i j r t k=p k := by simp only [move, sign, ite_eq_right hki, ite_eq_right hkj, sub_self, mul_zero, add_zero]

omit [Fintype I] in
theorem move_bounds {p : I → ℝ} (hp : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    {i j : I} (hij : i ≠ j) {r t : ℝ} (hr : 0 < r)
    (ht0 : -down p i j r ≤ t) (ht1 : t ≤ up p i j r) :
    (∀ k, 0 ≤ move p i j r t k) ∧ (∀ k, move p i j r t k ≤ 1) := by
  have hl1 := min_le_left (p i) ((1-p j)/r)
  have hl2 := (le_div_iff₀ hr).mp (min_le_right (p i) ((1-p j)/r))
  have hu1 := min_le_left (1-p i) (p j/r)
  have hu2 := (le_div_iff₀ hr).mp (min_le_right (1-p i) (p j/r))
  have htl := mul_le_mul_of_nonneg_left ht0 hr.le
  have htu := mul_le_mul_of_nonneg_left ht1 hr.le
  change -min (p i) ((1-p j)/r) ≤ t at ht0
  change t ≤ min (1-p i) (p j/r) at ht1
  change r * -min (p i) ((1-p j)/r) ≤ r*t at htl
  change r*t ≤ r*min (1-p i) (p j/r) at htu
  constructor <;> intro k <;> by_cases hki : k=i
  · subst k; rw [move_left p hij]; linarith only [ht0, hl1]
  · by_cases hkj : k=j
    · subst k; rw [move_right p hij]; nlinarith only [htu, hu2]
    · rw [move_other p hki hkj]; exact hp k
  · subst k; rw [move_left p hij]; linarith only [ht1, hu1]
  · by_cases hkj : k=j
    · subst k; rw [move_right p hij]; nlinarith only [htl, hl2]
    · rw [move_other p hki hkj]; exact hp1 k

theorem fractional_subset {p : I → ℝ} {i j : I}
    (hi : i ∈ fractional p) (hj : j ∈ fractional p) (r t : ℝ) :
    fractional (move p i j r t) ⊆ fractional p := by
  intro k hk
  by_cases hki : k=i
  · simpa only [hki] using hi
  by_cases hkj : k=j
  · simpa only [hkj] using hj
  simpa only [mem_fractional, move_other p hki hkj] using hk

theorem up_smaller {p : I → ℝ} {i j : I} {r : ℝ} (hr : 0 < r) (hij : i ≠ j)
    (hi : i ∈ fractional p) (hj : j ∈ fractional p) :
    (fractional (move p i j r (up p i j r))).card < (fractional p).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨fractional_subset hi hj _ _, ?_⟩
  intro heq
  rcases le_total (1-p i) (p j/r) with h | h
  · have hv : move p i j r (up p i j r) i=1 := by rw [move_left p hij, up, min_eq_left h]; ring
    have hin := heq ▸ hi
    have hnot : i ∉ fractional (move p i j r (up p i j r)) := by simp only [mem_fractional, hv]; norm_num
    exact hnot hin
  · have hv : move p i j r (up p i j r) j=0 := by
      rw [move_right p hij, up, min_eq_right h, mul_div_cancel₀ _ (ne_of_gt hr), sub_self]
    have hin := heq ▸ hj
    have hnot : j ∉ fractional (move p i j r (up p i j r)) := by simp only [mem_fractional, hv]; norm_num
    exact hnot hin

theorem down_smaller {p : I → ℝ} {i j : I} {r : ℝ} (hr : 0 < r) (hij : i ≠ j)
    (hi : i ∈ fractional p) (hj : j ∈ fractional p) :
    (fractional (move p i j r (-down p i j r))).card < (fractional p).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨fractional_subset hi hj _ _, ?_⟩
  intro heq
  rcases le_total (p i) ((1-p j)/r) with h | h
  · have hv : move p i j r (-down p i j r) i=0 := by rw [move_left p hij, down, min_eq_left h]; ring
    have hin := heq ▸ hi
    have hnot : i ∉ fractional (move p i j r (-down p i j r)) := by simp only [mem_fractional, hv]; norm_num
    exact hnot hin
  · have hv : move p i j r (-down p i j r) j=1 := by
      rw [move_right p hij, down, min_eq_right h, mul_neg, mul_div_cancel₀ _ (ne_of_gt hr)]; ring
    have hin := heq ▸ hj
    have hnot : j ∉ fractional (move p i j r (-down p i j r)) := by simp only [mem_fractional, hv]; norm_num
    exact hnot hin

end MetricKMedian.WeightedRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalSignedStep
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
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

theorem endpoint_feasible (β : Fin n → ℚ) 
    (p : Vector ℚ n) (hp : ∀ k, 0 ≤ point p k ∧ point p k ≤ 1) (b : Fin 2) :
    ∀ k, 0 ≤ point (endpoint β p b) k ∧ point (endpoint β p b) k ≤ 1 := by
  by_cases h : Active β p
  · let a := pair β p h
    let r := β a.val.1/β a.val.2
    have hr : 0 < r := pair_ratio_pos β p h
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
    have hh := WeightedRounding.move_bounds hpr0 hpr1 a.property.2.2.1 hrr ht0r ht1r
    rw [← real_move] at hh
    simp only [realPoint] at hh
    intro k
    simp only [endpoint,dite_eq_left h]
    exact ⟨by exact_mod_cast hh.1 k,by exact_mod_cast hh.2 k⟩
  · simpa only [endpoint,dite_eq_right h] using hp

theorem endpoint_smaller (β : Fin n → ℚ) 
    (p : Vector ℚ n) (h : Active β p) (b : Fin 2) :
    (fractional (endpoint β p b)).card < (fractional p).card := by
  let a := pair β p h
  let r := β a.val.1/β a.val.2
  have hr : (0:ℝ) < r := by exact_mod_cast pair_ratio_pos β p h
  have hi : a.val.1 ∈ MarginalRounding.fractional (realPoint p) := by
    rw [real_fractional]; exact a.property.1
  have hj : a.val.2 ∈ MarginalRounding.fractional (realPoint p) := by
    rw [real_fractional]; exact a.property.2.1
  simp only [endpoint,dite_eq_left h]
  by_cases hb : b=0
  · rw [ite_eq_left hb]
    have hh := WeightedRounding.up_smaller hr a.property.2.2.1 hi hj
    simpa only [← real_up,← real_move,real_fractional] using hh
  · rw [ite_eq_right hb]
    have hh := WeightedRounding.down_smaller hr a.property.2.2.1 hi hj
    simpa only [← real_down,← Rat.cast_neg,← real_move,real_fractional] using hh

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
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseGraphFeatures
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
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

def edge (G : Graph n m) (h : Fin n) (i : Fin m) : ℚ := if h ∈ G i then 1 else 0

def edgeCode (G : Graph n m) (a : Fin (n*m)) : ℚ :=
  edge G (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2

def features (G : Graph n m) (a : Fin (n*m+(n*m)*(n*m))) : ℚ :=
  Sum.elim (edgeCode G) (fun ij : Fin ((n*m)*(n*m)) =>
    edgeCode G (finProdFinEquiv.symm ij).1*edgeCode G (finProdFinEquiv.symm ij).2)
    (finSumFinEquiv.symm a)

@[simp] theorem features_single (G : Graph n m) (h : Fin n) (i : Fin m) :
    features G (finSumFinEquiv (Sum.inl (finProdFinEquiv (h,i))))=edge G h i := by
  simp only [features,edgeCode,Equiv.symm_apply_apply,Sum.elim_inl]

@[simp] theorem features_pair (G : Graph n m) (h k : Fin n) (i j : Fin m) :
    features G (finSumFinEquiv (Sum.inr (finProdFinEquiv
      (finProdFinEquiv (h,i),finProdFinEquiv (k,j)))))=edge G h i*edge G k j := by
  simp only [features,edgeCode,Equiv.symm_apply_apply,Sum.elim_inr]

def next (G : Graph n m) (S : Finset (Fin n)) (i : Fin m) : Graph n m :=
  Function.update G i S

@[simp] theorem edge_next (G : Graph n m) (S : Finset (Fin n)) (h : Fin n) (i j : Fin m) :
    edge (next G S i) h j=if j=i then (if h∈S then 1 else 0) else edge G h j := by
  by_cases hji : j=i <;> simp [edge,next,hji]

end MetricKMedian.SparseGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CopyState
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential
variable {F : Type*} [DecidableEq F]
variable (Δ : ℕ)

variable [Fintype F]

def next (A erased : Finset (Copy (F := F) Δ)) (O : Finset F) := (A \ erased) ∪ resets Δ O

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalCopyTransition
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

def erased (A : Finset (CopyState.Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graph G) H)) : Finset (CopyState.Copy (F := F) Δ) :=
  (Z.biUnion (heavy (graph G) H).erase).image Subtype.val

def opened (A : Finset (CopyState.Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graph G) H)) : Finset F :=
  (sources G H Z).image (fun i => i.val.1)

def transition (A : Finset (CopyState.Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graph G) H)) : Finset (CopyState.Copy (F := F) Δ) :=
  CopyState.next Δ A (erased A G H Z) (opened A G H Z)

end MetricKMedian.RationalBatchData
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBernoulliFeatures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

def target (p : Fin n → ℚ) (t : ℕ) (f : Fin d → Fin (n+1)) : ℚ :=
  ∏ i ∈ used f, if i.val<t then p i else 0

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalTaperAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset

variable {I : Type*} [Fintype I]

def A (P : ℚ) (d : I → ℚ) (t : ℚ) : ℚ := ∑ i, aCoef P (d i) t

def B (P : ℚ) (d : I → ℚ) (t : ℚ) : ℚ := ∑ i, bCoef P (d i) t

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalTaperCandidates
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type*} [Fintype I]

def candidates (g P : ℚ) (d : I → ℚ) : Finset ℚ :=
  breakpoints P d ∪ ((breakpoints P d) ×ˢ (breakpoints P d)).image
    (fun p => (A P d ((p.1+p.2)/2)-1/g)/B P d ((p.1+p.2)/2))

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalTaper
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type*} [Fintype I]

def rationalMass (g P : ℚ) (d : I → ℚ) (r : ℚ) : ℚ :=
  ∑ i, g*rationalMarginal P (d i) r

def rootCandidates (g P : ℚ) (d : I → ℚ) : Finset ℚ :=
  (candidates g P d).filter (fun q => 0 < q ∧ rationalMass g P d q=1)

def inverseRadius (g P : ℚ) (d : I → ℚ) : ℚ :=
  if h : (rootCandidates g P d).Nonempty then (rootCandidates g P d).max' h else 0

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalTaperData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type*} [Fintype I] [LinearOrder I]

def sourceMarginals (g P : ℚ) (d : I → ℚ) (own : Finset I) (Δ : ℕ) : I → ℚ :=
  if 1 ≤ rationalColocatedMass g d then zeroMarginal d own Δ
  else fun i => rationalMarginal P (d i) (inverseRadius g P d)

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseEnumeratedGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedGraph
open Finset
variable {I : Type} [DecidableEq I] {n : ℕ}

def lift (enum : Fin n ≃ I) (G : SparseGraph.Graph n n) : I → Finset I :=
  fun i => (G (enum.symm i)).map enum.toEmbedding

omit [DecidableEq I] in
@[simp] theorem mem_lift (enum : Fin n ≃ I) (G : SparseGraph.Graph n n) (h i : I) :
    h∈lift enum G i ↔ enum.symm h∈G (enum.symm i) := by
  simp only [lift,mem_map,Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨a,ha,he⟩
    simpa only [← he,Equiv.symm_apply_apply] using ha
  · intro ha
    exact ⟨enum.symm h,ha,enum.apply_symm_apply h⟩

end MetricKMedian.SparseEnumeratedGraph
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

def extend (h : History α) (a : α) : History α := (a,h.1::h.2)

end MetricKMedian.SparseHistories
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

local instance instLinearOrderCopy_rcbf2c5_1 : LinearOrder (CopyState.Copy (F := F) Δ) := copyOrder
def own (A : Finset (CopyState.Copy (F := F) Δ)) (i : A) : Finset A :=
  univ.filter (fun h => h.val.1=i.val.1)

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalSignedTerminal
attribute [-simp] _root_.OAI.MetricKMedian.SparseTargetSubset.point_initial _root_.OAI.MetricKMedian.SparseWeightedPartial.features_pair _root_.OAI.MetricKMedian.SparseWeightedPartial.features_single
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

def state (u : Fin n → ℚ) (p : Vector ℚ n) (ω : Fin n → Bool) : Vector ℚ n :=
  Vector.ofFn (fun i => if u i<0 then point p i else SparseBernoulli.flag ω i)

@[simp] theorem point_state (u : Fin n → ℚ) (p : Vector ℚ n) (ω : Fin n → Bool) (i : Fin n) :
    point (state u p ω) i=(if u i<0 then point p i else SparseBernoulli.flag ω i) := by
  simp only [state,point,Vector.getElem_ofFn,Fin.eta]

end MetricKMedian.RationalSignedTerminal
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparedDataOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.SparsePrepared.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (indices)

abbrev BaseRaw := BTable × (QRow × (BTable × (QRow × (QRow × ℕ))))
end MetricKMedian.SparsePrepared.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RationalSupplierPreparation
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                   
section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars
variable {f n : ℕ}

def index : Fin (size f n) ≃ Star (Fin f) (Fin n) :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) <|
    finSumFinEquiv.symm.trans (Equiv.sumCongr finProdFinEquiv.symm (Equiv.refl _)))

def D (A : Fin n → Finset (Fin f)) : Fin (size f n) → Finset (Fin n) := targets A ∘ index

def a : Fin (size f n) → ℚ := flagQ ∘ index

def q (y : Fin f → ℚ) (P A : Fin n → Finset (Fin f)) (c : Fin n → ℚ)
    (γ g : ℚ) (e : Fin (size f n)) : ℚ := weightQ y P A c γ (index e) / g

theorem a_bounds (e : Fin (size f n)) : 0 ≤ a e ∧ a e ≤ 1 := by
  dsimp only [a, Function.comp_apply]
  generalize index e = z
  cases z <;> norm_num [flagQ]

theorem q_nonneg (y : Fin f → ℚ) (P A : Fin n → Finset (Fin f))
    (c : Fin n → ℚ) (γ g : ℚ) (hy : ∀ i, 0 ≤ y i) (hc : ∀ t, 0 ≤ c t)
    (hγ : 0 ≤ γ) (hg : 0 ≤ g) (e : Fin (size f n)) : 0 ≤ q y P A c γ g e := by
  apply div_nonneg _ hg
  have hw := weight_nonneg (fun i => (y i : ℝ)) P A (fun t => (c t : ℝ)) (γ : ℝ)
    (fun i => by exact_mod_cast hy i) (fun t => by exact_mod_cast hc t)
    (by exact_mod_cast hγ) (index e)
  rw [← weight_cast] at hw
  exact_mod_cast hw

end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end


