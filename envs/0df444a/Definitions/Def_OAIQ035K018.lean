-- Prove2me | Definitions.Def_OAIQ035K018
-- name    : OAIQ035K018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:56:06.154558+00:00
-- url     : https://prove2.me/theorems/e05a33cb-b7d0-473e-be60-431510d68c1b
-- title:
--   Definitions bundle OAIQ035K018 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 7 definitions, 1 inductive type or structure and 12 theorems. The definitions and types are `OAI.MetricKMedian.Gaussian.computedIntegerKernel`, `OAI.MetricKMedian.Gaussian.kernelVector`, `OAI.MetricKMedian.IntegerLaw.ListOperation.Rows`, `OAI.MetricKMedian.IntegerLaw.computedAffineKernel`, `OAI.MetricKMedian.IntegerLaw.computedPivot`, `OAI.MetricKMedian.IntegerLaw.leastRatio`, `OAI.MetricKMedian.IntegerLaw.pivotSet`, `OAI.MetricKMedian.SparseBernoulli.Program.Context`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Compression_AffineListOperations`, `KMedian_Compression_ComputedAffineKernel`, `KMedian_Compression_ComputedIntegerKernel`, `KMedian_Compression_ComputedPivot`, `KMedian_Compression_GaussianCircuit`, `KMedian_Compression_GaussianKernel`, `KMedian_Compression_GaussianTabulated`, `KMedian_Compression_RationalScaling`, `KMedian_Probability_BernoulliStepProgram`.
--
--   **Imports.** It imports the bundles `OAIQ035K000`, `OAIQ035K001`, `OAIQ035K002`, `OAIQ035K003`, `OAIQ035K005` and `OAIQ035K006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K030`, `OAIQ035K031` and `OAIQ035K032`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K000
import Definitions.Def_OAIQ035K001
import Definitions.Def_OAIQ035K002
import Definitions.Def_OAIQ035K003
import Definitions.Def_OAIQ035K005
import Definitions.Def_OAIQ035K006

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Gaussian
open Finset

theorem lift_nonzero {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ) (p : Fin (n+1))
    (z : Fin n → ℚ) (hz : ∃ j, z j ≠ 0) : ∃ j, lift A p z j ≠ 0 := by
  obtain ⟨j,hj⟩ := hz
  exact ⟨p.succAbove j, by simpa only [lift,Fin.insertNth_apply_succAbove] using hj⟩

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

theorem kernel_spec (r n : ℕ) (A : Fin r → Fin n → ℚ) (hn : r < n) :
    (∃ j, kernel r n A j ≠ 0) ∧ (∀ i, ∑ j, A i j*kernel r n A j=0) := by
  induction r generalizing n with
  | zero =>
    have hn0 : 0 < n := hn
    refine ⟨⟨⟨0,hn0⟩,?_⟩,fun i => Fin.elim0 i⟩
    simp only [kernel,ite_true,ne_eq,one_ne_zero,not_false_eq_true]
  | succ r ih =>
    cases n with
    | zero => omega
    | succ n =>
      by_cases hh : (univ.filter (fun j => A 0 j ≠ 0)).Nonempty
      · let p := (univ.filter (fun j => A 0 j ≠ 0)).min' hh
        have hp : A 0 p ≠ 0 := (mem_filter.mp (min'_mem _ hh)).2
        have hi := ih n (residual A p) (by omega)
        change (∃ j, (if h : (univ.filter (fun j => A 0 j ≠ 0)).Nonempty then
            lift A ((univ.filter (fun j => A 0 j ≠ 0)).min' h)
              (kernel r n (residual A ((univ.filter (fun j => A 0 j ≠ 0)).min' h)))
            else kernel r (n+1) (fun i j => A i.succ j)) j ≠ 0) ∧ _
        simp only [kernel,dite_eq_left hh]
        exact ⟨lift_nonzero A p _ hi.1,lift_kernel A p hp _ hi.2⟩
      · have hzero : ∀ j, A 0 j=0 := by
          intro j
          by_contra hj
          exact hh ⟨j,mem_filter.mpr ⟨mem_univ _,hj⟩⟩
        have hi := ih (n+1) (fun i j => A i.succ j) (by omega)
        have he : kernel (r+1) (n+1) A=kernel r (n+1) (fun i j => A i.succ j) := by
          rw [kernel,dite_eq_right hh]
        rw [he]
        refine ⟨hi.1,?_⟩
        intro i
        refine Fin.cases ?_ (fun i => hi.2 i) i
        simp only [hzero,zero_mul,sum_const_zero]

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
-- module Solutions.OAIQ035_KM.KMedian_Compression_GaussianTabulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Gaussian
open Finset

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
-- module Solutions.OAIQ035_KM.KMedian_Compression_RationalScaling
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
-- module Solutions.OAIQ035_KM.KMedian_Compression_ComputedIntegerKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Gaussian
open Finset

def computedIntegerKernel (r n : ℕ) (V : Fin r → Fin n → ℤ) : Fin n → ℤ :=
  let A := tabulate (fun i j => (V i j:ℚ))
  let q := kernelVector r n A
  let b := Vector.ofFn (RationalScaling.numerator (fun j => q[j.val]))
  fun j => b[j.val]

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

def computedAffineKernel {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℤ) : Fin n → ℤ :=
  let zi := Gaussian.computedIntegerKernel (d+1) μ.support.card (activeMatrix μ v)
  let z := Vector.ofFn (Compression.extendVector μ.support zi)
  fun i => z[i.val]

end MetricKMedian.IntegerLaw

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
abbrev Rows := Binary.IntegerList.Rows

end MetricKMedian.IntegerLaw.ListOperation
end

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

theorem positiveSet_nonempty {n : ℕ} (z : Fin n → ℤ)
    (hsum : ∑ i, z i=0) (hne : ∃ i, z i ≠ 0) : (positiveSet z).Nonempty := by
  obtain ⟨i,hi⟩ := positive_entry hsum hne
  exact ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩⟩

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

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliStepProgram
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

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end


