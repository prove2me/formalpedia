-- Prove2me | Definitions.Def_OAIQ053K030
-- name    : OAIQ053K030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:59:12.948627+00:00
-- url     : https://prove2.me/theorems/79b4e356-e9e1-4f6f-b183-a2b628810134
-- title:
--   Definitions bundle OAIQ053K030 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 24 declarations of OpenAI's Lean: 11 definitions, 1 inductive type or structure and 12 theorems. The definitions and types are `OAI.MetricKMedian.FixedBatch.RationalParameters.completedGood`, `OAI.MetricKMedian.FixedBatch.RationalParameters.taperAt`, `OAI.MetricKMedian.Preparation.FractionalRefinement.count`, `OAI.MetricKMedian.Preparation.FractionalRefinement.original`, `OAI.MetricKMedian.Preparation.FractionalRefinement.realization`, `OAI.MetricKMedian.Preparation.FractionalRefinement.unitInput`, `OAI.MetricKMedian.Preparation.FractionalRefinement.x`, `OAI.MetricKMedian.Preparation.RationalAllParameters`, `OAI.MetricKMedian.Preparation.computedNearest`, `OAI.MetricKMedian.Preparation.fill`, `OAI.MetricKMedian.RationalPhysicalKernel.completed`, `OAI.MetricKMedian.SparseIntegerLaw.trim`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Compression_CircuitBitBound`, `KMedian_Compression_ComputedAffineKernel`, `KMedian_Compression_ComputedIntegerKernel`, `KMedian_Compression_DependentIntegerKernel`, `KMedian_Compression_GaussianKernel`, `KMedian_Geometry_RationalAllParameters`, `KMedian_Geometry_RationalFractionalInput`, `KMedian_Geometry_RationalHistoryCompletion`, `KMedian_Geometry_RationalHistorySelection`, `KMedian_Geometry_RationalParameterizedHistory`, `KMedian_Optimization_ComputedNearest`, `KMedian_Programs_RationalSortProgram`, `KMedian_Sparse_SparseIntegerLaw`.
--
--   **Imports.** It imports the bundles `OAIQ053K014`, `OAIQ053K015`, `OAIQ053K016` and `OAIQ053K017` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K039`, `OAIQ053K040`, `OAIQ053K041` and `OAIQ053K042`; the statement `OAI.MetricKMedian.Preparation.exists_rational_all_parameters_s53`; the proof of `OAI.MetricKMedian.Preparation.exists_rational_all_parameters_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K014
import Definitions.Def_OAIQ053K015
import Definitions.Def_OAIQ053K016
import Definitions.Def_OAIQ053K017

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_DependentIntegerKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Compression
open Finset Matrix

theorem full_integer_kernel_of_dependent {R Ω : Type} [Fintype R] [Fintype Ω]
    (V : Matrix R Ω ℤ) (L : ℕ) (hV : ∀ r i, |V r i| ≤ (2:ℤ)^L)
    (hdep : ¬ LinearIndependent ℚ (fun i r => (V r i:ℚ))) :
    ∃ z : Ω → ℤ, (∃ i, z i ≠ 0) ∧
      (∀ i, |z i| ≤ (2:ℤ)^(2*Fintype.card R*(Fintype.card R+L))) ∧
      ∀ r, ∑ i, z i*V r i=0 := by
  classical
  obtain ⟨K,inst,a,z,ha,_,hne,hbound,hker⟩ := small_integer_dependence_of_dependent V L hV hdep
  let zz : Ω → ℤ := fun i => ∑ k, if a k=i then z k else 0
  have hzval : ∀ k, zz (a k)=z k := by
    intro k
    simp only [zz,ha.eq_iff]
    simpa only [mem_univ,ite_true] using sum_ite_eq' univ k z
  have hzout : ∀ i, (¬∃ k, a k=i) → zz i=0 := by
    intro i hi
    apply sum_eq_zero
    intro k _
    exact ite_eq_right (fun hk => hi ⟨k,hk⟩)
  refine ⟨zz,?_,?_,?_⟩
  · obtain ⟨k,hk⟩ := hne
    exact ⟨a k,by rwa [hzval]⟩
  · intro i
    by_cases hi : ∃ k, a k=i
    · obtain ⟨k,rfl⟩ := hi
      rw [hzval]
      exact hbound k
    · rw [hzout i hi,abs_zero]
      positivity
  · intro r
    change (∑ i, (∑ k, if a k=i then z k else 0)*V r i)=0
    simp only [sum_mul,ite_mul,zero_mul]
    rw [sum_comm]
    simpa using hker r

end MetricKMedian.Compression

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianKernel
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Gaussian
open Finset

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
-- module Solutions.OAIQ053_KM.KMedian_Compression_CircuitBitBound
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Gaussian
open Finset

theorem circuit_integer_ratio {r n : ℕ} (V : Fin r → Fin n → ℤ)
    (z : Fin n → ℚ) (L : ℕ) (hV : ∀ i j, |V i j| ≤ (2:ℤ)^L)
    (hz : ∀ i, ∑ j, (V i j:ℚ)*z j=0)
    (hc : IsCircuit (fun i j => (V i j:ℚ)) z) (w : Fin n) (hw : z w=1) :
    ∃ U : Fin n → ℤ, U w ≠ 0 ∧
      (∀ j, |U j| ≤ (2:ℤ)^(2*r*(r+L))) ∧
      ∀ j, z j=(U j:ℚ)/(U w:ℚ) := by
  classical
  let S := univ.filter (fun j => z j ≠ 0)
  have hwS : w ∈ S := by simp only [S,mem_filter,mem_univ,true_and,hw,ne_eq,one_ne_zero,not_false_eq_true]
  have hdep : ¬ LinearIndependent ℚ (fun j : ↥S => fun i => (V i j.val:ℚ)) := by
    intro hi
    have hsum : ∑ j : ↥S, z j.val • (fun i => (V i j.val:ℚ))=0 := by
      funext i
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply]
      rw [sum_coe_sort S (fun j => z j*(V i j:ℚ))]
      have he : (∑ j ∈ S, z j*(V i j:ℚ))=∑ j, z j*(V i j:ℚ) := by
        apply sum_subset (subset_univ _)
        intro j _ hj
        have he : z j=0 := by simpa only [S,mem_filter,mem_univ,true_and,not_not] using hj
        rw [he,zero_mul]
      rw [he]
      simpa only [mul_comm] using hz i
    have hh := (Fintype.linearIndependent_iff.mp hi) (fun j => z j.val) hsum ⟨w,hwS⟩
    rw [hw] at hh
    exact one_ne_zero hh
  obtain ⟨u,hune,hb,hker⟩ := Compression.full_integer_kernel_of_dependent
    (fun i (j : ↥S) => V i j.val) L (fun i j => hV i j.val) hdep
  let U : Fin n → ℤ := fun j => if h : j ∈ S then u ⟨j,h⟩ else 0
  have hUval : ∀ j : ↥S, U j.val=u j := by intro j; simp only [U,dite_eq_left j.property]
  have hUne : ∃ j, U j ≠ 0 := by
    obtain ⟨j,hj⟩ := hune
    exact ⟨j.val,by rwa [hUval]⟩
  have hUz : ∀ j, z j=0 → U j=0 := by
    intro j hj
    have hn : j ∉ S := by simp only [S,mem_filter,mem_univ,true_and,hj,ne_eq,not_true_eq_false,not_false_eq_true]
    exact dite_eq_right hn
  have hUker : ∀ i, ∑ j, (V i j:ℚ)*(U j:ℚ)=0 := by
    intro i
    have hh : (∑ j, U j*V i j)=∑ j : ↥S, u j*V i j.val := by
      calc
        _ = ∑ j ∈ S, U j*V i j := by
          symm
          apply sum_subset (subset_univ _)
          intro j _ hj
          simp only [U,dite_eq_right hj,zero_mul]
        _ = _ := by rw [← sum_coe_sort]; exact sum_congr rfl (fun j _ => by rw [hUval])
    have hh' := hh.trans (hker i)
    have hcast : (∑ j, (U j:ℚ)*(V i j:ℚ))=0 := by exact_mod_cast hh'
    simpa only [mul_comm] using hcast
  obtain ⟨t,ht⟩ := hc (fun j => (U j:ℚ)) (by intro j hj; exact_mod_cast hUz j hj) hUker
  have htw : (U w:ℚ)=t := by simpa only [hw,mul_one] using ht w
  have htn : t ≠ 0 := by
    intro ht0
    obtain ⟨j,hj⟩ := hUne
    have hh := ht j
    rw [ht0,zero_mul] at hh
    exact hj (by exact_mod_cast hh)
  have hUw : U w ≠ 0 := by intro hn; simp only [hn,Int.cast_zero] at htw; exact htn htw.symm
  refine ⟨U,hUw,?_,?_⟩
  · intro j
    by_cases hj : j ∈ S
    · rw [show U j=u ⟨j,hj⟩ from dite_eq_left hj]
      simpa only [Fintype.card_fin] using hb ⟨j,hj⟩
    · rw [show U j=0 from dite_eq_right hj,abs_zero]; positivity
  · intro j
    rw [htw]
    apply (eq_div_iff htn).mpr
    rw [ht j]
    ring

theorem integer_input_kernel_bounds (r n L : ℕ) (V : Fin r → Fin n → ℤ)
    (hn : r < n) (hV : ∀ i j, |V i j| ≤ (2:ℤ)^L) :
    let z := kernel r n (fun i j => (V i j:ℚ))
    ∀ j, |(z j).num| ≤ (2:ℤ)^(2*r*(r+L)) ∧
      ((z j).den:ℤ) ≤ (2:ℤ)^(2*r*(r+L)) := by
  dsimp only
  obtain ⟨⟨w,hw⟩,hc⟩ := kernel_circuit r n (fun i j => (V i j:ℚ)) hn
  have hk := (kernel_spec r n (fun i j => (V i j:ℚ)) hn).2
  obtain ⟨U,hUw,hU,hz⟩ := circuit_integer_ratio V _ L hV hk hc w hw
  intro j
  rw [hz j]
  exact ratio_num_den_bound (U j) (U w) hUw _ (hU j) (hU w)

end MetricKMedian.Gaussian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_ComputedIntegerKernel
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Gaussian
open Finset

theorem computedIntegerKernel_spec (r n L : ℕ) (V : Fin r → Fin n → ℤ)
    (hn : r < n) (hV : ∀ i j, |V i j| ≤ (2:ℤ)^L) :
    (∃ j, computedIntegerKernel r n V j ≠ 0) ∧
      (∀ i, ∑ j, computedIntegerKernel r n V j*V i j=0) ∧
      ∀ j, |computedIntegerKernel r n V j| ≤ (2:ℤ)^((2*r*(r+L))*(n+1)) := by
  let q := kernel r n (fun i j => (V i j:ℚ))
  have he : computedIntegerKernel r n V=RationalScaling.numerator q := by
    funext j
    dsimp only [computedIntegerKernel]
    simp only [Vector.getElem_ofFn,kernelVector_eq,values_tabulate]
    rfl
  rw [he]
  have hq := kernel_spec r n (fun i j => (V i j:ℚ)) hn
  have hb := integer_input_kernel_bounds r n L V hn hV
  let D := RationalScaling.denominator q
  have hD : (D:ℚ) ≠ 0 := by exact_mod_cast (RationalScaling.denominator_pos q).ne'
  have heq : ∀ j, (RationalScaling.numerator q j:ℚ)=q j*(D:ℚ) :=
    RationalScaling.numerator_cast q
  refine ⟨?_,?_,?_⟩
  · obtain ⟨j,hj⟩ := hq.1
    refine ⟨j,?_⟩
    intro hz
    have hh := heq j
    rw [hz,Int.cast_zero] at hh
    exact (mul_ne_zero hj hD) hh.symm
  · intro i
    have hi : (∑ j, (RationalScaling.numerator q j:ℚ)*(V i j:ℚ))=0 := by
      simp only [heq]
      calc
        _ = (∑ j, (V i j:ℚ)*q j)*(D:ℚ) := by
          rw [sum_mul]; apply sum_congr rfl; intro j _; ring
        _ = 0 := by rw [hq.2 i,zero_mul]
    exact_mod_cast hi
  · intro j
    simpa only [Fintype.card_fin] using RationalScaling.numerator_bound q (2*r*(r+L))
      (fun j => (hb j).1) (fun j => (hb j).2) j

end MetricKMedian.Gaussian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_ComputedAffineKernel
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
attribute [-simp] _root_.OAI.MetricKMedian.IntegerLaw.eliminateAt_numerator _root_.OAI.MetricKMedian.IntegerLaw.trim_denominator _root_.OAI.MetricKMedian.IntegerLaw.trim_numerator _root_.OAI.MetricKMedian.IntegerLaw.trim_weight _root_.OAI.MetricKMedian.RationalLaw.integer_numerator_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

theorem computedAffineKernel_spec {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℤ) (L : ℕ) (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L)
    (hsize : d+1 < μ.support.card) :
    let z := computedAffineKernel μ v
    (∃ i, z i ≠ 0) ∧ (∑ i, z i=0) ∧
      (∀ j, ∑ i, (z i:ℚ)*(v i j:ℚ)=0) ∧
      (∀ i, μ.numerator i=0 → z i=0) ∧
      ∀ i, |z i| ≤ (2:ℤ)^((2*(d+1)*(d+1+L))*(n+1)) := by
  dsimp only
  let V := activeMatrix μ v
  let zi := Gaussian.computedIntegerKernel (d+1) μ.support.card V
  have hVb : ∀ j i, |V j i| ≤ (2:ℤ)^L := by
    intro j i
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [V,activeMatrix,Fin.cases_zero,abs_one] using
        (one_le_pow₀ (by norm_num : (1:ℤ) ≤ 2) : (1:ℤ) ≤ 2^L)
    · simpa only [V,activeMatrix,Fin.cases_succ] using hv ((μ.support.orderIsoOfFin rfl) i).val j
  have hzi := Gaussian.computedIntegerKernel_spec (d+1) μ.support.card L V hsize hVb
  have he : computedAffineKernel μ v=Compression.extendVector μ.support zi := by
    funext i
    simp only [computedAffineKernel,Vector.getElem_ofFn]
    rfl
  rw [he]
  refine ⟨?_,?_,?_,?_,?_⟩
  · obtain ⟨i,hi⟩ := hzi.1
    exact ⟨((μ.support.orderIsoOfFin rfl) i).val,by rwa [Compression.extendVector_at]⟩
  · have hh := hzi.2.1 0
    simp only [V,activeMatrix,Fin.cases_zero,mul_one] at hh
    simpa only [mul_one] using
      (Compression.extendVector_sum μ.support zi (fun _ => 1)).trans (by simpa only [mul_one] using hh)
  · intro j
    have hh := hzi.2.1 j.succ
    simp only [V,activeMatrix,Fin.cases_succ] at hh
    have ht := (Compression.extendVector_sum μ.support zi (fun i => v i j)).trans hh
    exact_mod_cast ht
  · intro i hi
    apply Compression.extendVector_zero
    simpa only [mem_support,not_not] using hi
  · intro i
    have heN : μ.support.card ≤ n := (card_le_univ _).trans_eq (Fintype.card_fin n)
    apply Compression.extendVector_bound _ _ _ (by positivity) _ i
    intro j
    exact (hzi.2.2 j).trans (pow_le_pow_right₀ (by norm_num)
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right heN 1)))

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalAllParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation

structure RationalAllParameters (η τ : ℝ) where
  round : FixedBatch.RationalParameters τ
  even : Even round.Δ
  M : ℚ
  δ : ℚ
  γ : ℚ
  T₁ : ℚ
  hM : 0<M
  hδ : 0<δ
  hδ1 : (δ:ℝ)≤1/4
  hγ : 0<γ
  hγ1 : γ≤1
  hT : 0<T₁
  hθ : 1/((M:ℝ)*(δ:ℝ))≤1/8
  hα : (M:ℝ)/((δ:ℝ)*(T₁:ℝ))≤1/4
  failure : failureFactor (γ:ℝ) (round.g:ℝ)<1
  error : max (farFactor (δ:ℝ) (1-1/((M:ℝ)*(δ:ℝ)))
              ((M:ℝ)/((δ:ℝ)*(T₁:ℝ))) ((M:ℝ)/(T₁:ℝ)) (γ:ℝ))
          (nearFactor (1-1/((M:ℝ)*(δ:ℝ))) ((M:ℝ)+(1+(δ:ℝ))*(T₁:ℝ)) (γ:ℝ) (round.g:ℝ)) /
          (1-failureFactor (γ:ℝ) (round.g:ℝ)) ≤ 1+η

end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_ComputedNearest
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {n : ℕ}

def fill (U : Finset (Fin n)) (y d : Fin n → ℚ) (t : ℚ)
    (hy : ∀ i ∈ U, 0 ≤ y i) (ht : 0 ≤ t) (hm : t ≤ ∑ i ∈ U, y i) : Filling U y d t := by
  if hU : U.Nonempty then
    let a := firstNearest U d hU
    have ha : a ∈ U := (firstNearest_spec U d hU).1
    have hmin : ∀ i ∈ U, d a ≤ d i := (firstNearest_spec U d hU).2
    if hsmall : t ≤ y a then
      let x : Fin n → ℚ := fun i => if i=a then t else 0
      refine ⟨x,?_,?_,?_,?_⟩
      · intro i hi
        exact ite_eq_right (fun (he : i=a) => hi (he.symm ▸ ha))
      · intro i hi
        by_cases he : i=a
        · subst i
          simpa only [x,ite_eq_left rfl] using And.intro ht hsmall
        · simp only [x,ite_eq_right he]
          exact ⟨le_rfl,hy i hi⟩
      · simp only [x,sum_ite_eq',ite_eq_left ha]
      · intro i hi b hb hix _
        have hei : i=a := by
          by_contra he
          simp only [x,ite_eq_right he,lt_self_iff_false] at hix
        subst i
        exact hmin b hb
    else
      have hlt : y a < t := lt_of_not_ge hsmall
      have hm' : t-y a ≤ ∑ i ∈ U.erase a, y i := by
        have hs := sum_erase_add U y ha
        linarith only [hm,hs]
      let z := fill (U.erase a) y d (t-y a) (fun i hi => hy i (mem_of_mem_erase hi))
        (sub_nonneg.mpr hlt.le) hm'
      let x : Fin n → ℚ := Function.update z.amount a (y a)
      have hxa : x a=y a := Function.update_self _ _ _
      have hxi : ∀ i, i ≠ a → x i=z.amount i := fun i hi => Function.update_of_ne hi _ _
      refine ⟨x,?_,?_,?_,?_⟩
      · intro i hi
        rw [hxi i (fun (he : i=a) => hi (he.symm ▸ ha))]
        exact z.outside i (fun he => hi (mem_of_mem_erase he))
      · intro i hi
        by_cases he : i=a
        · subst i; rw [hxa]; exact ⟨hy a ha,le_rfl⟩
        · rw [hxi i he]
          exact z.bounds i (mem_erase.mpr ⟨he,hi⟩)
      · rw [← sum_erase_add U x ha,hxa]
        have he : (∑ i ∈ U.erase a, x i)=∑ i ∈ U.erase a, z.amount i :=
          sum_congr rfl (fun i hi => hxi i (mem_erase.mp hi).1)
        rw [he,z.total]
        ring
      · intro i hi b hb hix hbx
        by_cases he : i=a
        · subst i; exact hmin b hb
        · have hbe : b ≠ a := by
            intro hb'; subst b; rw [hxa] at hbx; exact lt_irrefl _ hbx
          rw [hxi i he] at hix
          rw [hxi b hbe] at hbx
          exact z.ordered i (mem_erase.mpr ⟨he,hi⟩) b (mem_erase.mpr ⟨hbe,hb⟩) hix hbx
  else
    have he : U=∅ := not_nonempty_iff_eq_empty.mp hU
    have ht0 : t=0 := le_antisymm (by simpa only [he,sum_empty] using hm) ht
    refine ⟨fun _ => 0,fun _ _ => rfl,?_,?_,?_⟩ <;> simp [he,ht0]
termination_by U.card
decreasing_by exact card_erase_lt_of_mem ha

def computedNearest (y d : Fin n → ℚ) (hy : ∀ i, 0 ≤ y i) (hm : 1 ≤ ∑ i, y i) : Vector ℚ n :=
  Vector.ofFn (fill univ y d 1 (fun i _ => hy i) (by norm_num) hm).amount

theorem computedNearest_spec (y d : Fin n → ℚ) (hy : ∀ i, 0 ≤ y i) (hm : 1 ≤ ∑ i, y i)
    (H : ℚ) :
    let x := computedNearest y d hy hm
    (∀ i : Fin n, 0 ≤ x[i.val] ∧ x[i.val] ≤ y i) ∧
    (∑ i : Fin n, x[i.val])=1 ∧
    (∑ i : Fin n, x[i.val]*d i)=FractionalDual.value d y H := by
  let a := fill univ y d 1 (fun i _ => hy i) (by norm_num) hm
  have hx := fun i => a.bounds i (mem_univ _)
  have hs := a.total
  have ho := fun i j => a.ordered i (mem_univ _) j (mem_univ _)
  dsimp only [computedNearest]
  simp only [Vector.getElem_ofFn]
  refine ⟨hx,hs,le_antisymm ?_ (FractionalDual.value_le_assignment d y a.amount H hx hs)⟩
  obtain ⟨i,hi⟩ := FractionalDual.ordered_attains d y a.amount hx hs ho
  rw [← hi]
  exact FractionalDual.affine_le_value d y H (d i) (by simp [FractionalDual.thresholds])

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalFractionalInput
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.Preparation
open Finset
variable {f j : ℕ}

 theorem computedNearest_ordered (y d : Fin f → ℚ) (hy : ∀ i, 0≤y i) (hm : 1≤∑ i, y i)
    (a b : Fin f) (ha : 0<(computedNearest y d hy hm)[a.val])
    (hb : (computedNearest y d hy hm)[b.val]<y b) : d a≤d b := by
  simp only [computedNearest,Vector.getElem_ofFn] at ha hb
  exact (fill univ y d 1 (fun i _ => hy i) (by norm_num) hm).ordered a (mem_univ _)
    b (mem_univ _) ha hb

namespace FractionalRefinement

variable (a : TruncatedLP.FractionalData f j) (k : ℕ) (ha : a.Valid k) (hj : 0<j)

def x (dc : Fin j → Fin f → ℚ) (c : Fin j) (i : Fin f) : ℚ :=
  (computedNearest (y a) (dc c) (fun b => (ha.1 b).1) (mass_one a k ha hj))[i.val]

 theorem x_spec (dc : Fin j → Fin f → ℚ) :
    (∀ c i, 0≤x a k ha hj dc c i ∧ x a k ha hj dc c i≤y a i) ∧
    (∀ c, ∑ i, x a k ha hj dc c i=1) ∧
    (∀ c b b', 0<x a k ha hj dc c b → x a k ha hj dc c b'<y a b' → dc c b≤dc c b') ∧
    (∑ c, ∑ i, x a k ha hj dc c i*dc c i)≤a.value dc := by
  have hs := fun c => computedNearest_spec (y a) (dc c) (fun b => (ha.1 b).1) (mass_one a k ha hj) 0
  refine ⟨fun c => (hs c).1,fun c => (hs c).2.1,?_,?_⟩
  · intro c b b' hb hb'
    exact computedNearest_ordered (y a) (dc c) (fun b => (ha.1 b).1) (mass_one a k ha hj) b b' hb hb'
  · apply sum_le_sum
    intro c _
    change (∑ i : Fin f, (computedNearest (y a) (dc c) _ _)[i.val]*dc c i)≤_
    rw [(hs c).2.2]
    exact FractionalDual.value_le_assignment (dc c) (y a) (fun i => a.assignment[c.val][i.val]) 0
      (ha.2.1 c) (ha.2.2.1 c)

def count (dc : Fin j → Fin f → ℚ) : ℕ :=
  RationalSplitting.count (y a) (x a k ha hj dc)

def original (dc : Fin j → Fin f → ℚ) : Fin (count a k ha hj dc) → Fin f :=
  RationalSplitting.original (y a) (x a k ha hj dc)

def unitInput (dc : Fin j → Fin f → ℚ) (dd : Fin j → Fin j → ℚ) (df : Fin f → Fin f → ℚ)
    (hdc : ∀ c i, 0≤dc c i) (hdd : ∀ c, dd c c=0) (hds : ∀ c c', dd c c'=dd c' c) :
    RationalUnitInput (count a k ha hj dc) j :=
  let hs := x_spec a k ha hj dc
  RationalSplitting.input (y a) (x a k ha hj dc) dc dd df (fun i => (ha.1 i).1) (fun i => (ha.1 i).2)
    (fun c i => (hs.1 c i).1) (fun c i => (hs.1 c i).2) hs.2.1 hdc hdd hds hs.2.2.1

 def realization {X : Type} [PseudoMetricSpace X]
    (dc : Fin j → Fin f → ℚ) (dd : Fin j → Fin j → ℚ) (df : Fin f → Fin f → ℚ)
    (hdc : ∀ c i, 0≤dc c i) (hdd : ∀ c, dd c c=0) (hds : ∀ c c', dd c c'=dd c' c)
    (i : Fin f → X) (c : Fin j → X)
    (hdf : ∀ b b', dist (i b) (i b')=(df b b':ℝ))
    (hc : ∀ c' b, dist (c c') (i b)=(dc c' b:ℝ))
    (hcc : ∀ c' c'', dist (c c') (c c'')=(dd c' c'':ℝ)) :
    (unitInput a k ha hj dc dd df hdc hdd hds).Realization X where
  i := fun b => i (original a k ha hj dc b)
  c := c
  hdf := fun first second => hdf (original a k ha hj dc first) (original a k ha hj dc second)
  hdc := fun client piece => hc client (original a k ha hj dc piece)
  hdd := hcc

end FractionalRefinement
end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseIntegerLaw
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian
open Finset

namespace SparseIntegerLaw
variable {α : Type}

def trim (μ : SparseIntegerLaw α) : SparseIntegerLaw α where
  length := μ.law.support.card
  states := Vector.ofFn (fun i => μ.states[(μ.law.support.orderEmbOfFin rfl i).val])
  law := μ.law.trim

end SparseIntegerLaw
end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalHistoryCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential CopyState Completion.Rational
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j Δ : ℕ}

local instance rationalHistoryCompletionCopyOrder_ra0873a_1 : LinearOrder (Copy (F := F) Δ) := copyOrder
def completed (d : Fin j → F → ℚ) (R : Fin j → ℚ)
    (B : Fin j → Finset (Copy (F := F) Δ)) (hB : ∀ c, (B c).Nonempty)
    (g β : ℚ) (z : SparseHistories.History (State F Δ g β)) : Finset F :=
  Completion.Rational.output d R z.1.1 B hB

end MetricKMedian.RationalPhysicalKernel
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalParameterizedHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                    
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
variable {τ : ℝ} (q : RationalParameters τ)

theorem probabilityQ_pos : 0 < q.probabilityQ := by
  have hh := q.hpos
  have hg := q.gpos
  exact_mod_cast (show 0 < 2*(q.h:ℝ)*(q.g:ℝ) by positivity)

theorem probabilityQ_le : (1+q.φ)*q.probabilityQ ≤ 1 := by
  exact_mod_cast q.probability

def taperAt (t : ℕ) : ℚ := if ht : t<q.T then q.taper ⟨t,ht⟩ else 1/2

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalHistorySelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
variable {τ : ℝ} (q : RationalParameters τ)
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j : ℕ}

local instance rationalHistorySelectionCopyOrder_ra0873a_1 : LinearOrder (Copy (F := F) q.Δ) := copyOrder
def completedGood (d : Fin j → F → ℚ) (R : Fin j → ℚ)
    (A : Finset (Copy (F := F) q.Δ)) (B : Fin j → Finset (Copy (F := F) q.Δ))
    (hB : ∀ c, (B c).Nonempty) (z : SparseHistories.History (State F q.Δ q.g q.β)) : Bool :=
  decide ((completed d R B hB q.g q.β z).Nonempty ∧
    ((completed d R B hB q.g q.β z).card:ℚ) ≤ q.g*A.card+q.allowance)

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_RationalSortProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.RationalSortProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly

 theorem filters_length {α : Type} (e : α → List Bool) (p q : α → Bool)
    (hd : ∀ a, ¬(p a=true ∧ q a=true)) (xs : List α) :
    (encodeList e (xs.filter p)).length+(encodeList e (xs.filter q)).length≤(encodeList e xs).length := by
  induction xs with
  | nil => simp [encodeList]
  | cons a xs ih =>
    have hh := hd a
    cases hp : p a <;> cases hq : q a <;>
      simp only [List.filter_cons,hp,hq,Bool.false_eq_true,ite_false,ite_true,
        EncodedList.cons_length] at ⊢
    · exact ih.trans (Nat.le_add_left _ _)
    · omega
    · omega
    · exact False.elim (hh ⟨hp,hq⟩)
end MetricKMedian.RationalSortProgram
end

end OAI
end


