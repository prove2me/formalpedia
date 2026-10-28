-- Prove2me | Definitions.Def_OAIQ035K030
-- name    : OAIQ035K030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:58:56.551893+00:00
-- url     : https://prove2.me/theorems/f4d59de8-1538-4049-8b32-6a0668470083
-- title:
--   Definitions bundle OAIQ035K030 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 10 definitions and 6 theorems. The definitions and types are `OAI.MetricKMedian.IntegerLaw.compressAuto`, `OAI.MetricKMedian.IntegerLaw.compressStepsAuto`, `OAI.MetricKMedian.IntegerLaw.compressionStepAuto`, `OAI.MetricKMedian.IntegerLaw.prod`, `OAI.MetricKMedian.RationalBatchData.ProposalProgram.Input.enumActions`, `OAI.MetricKMedian.RationalBatchData.erased`, `OAI.MetricKMedian.RationalLaw.sigma`, `OAI.MetricKMedian.SparseCardinalRounding.Program.br`, `OAI.MetricKMedian.SparseIntegerLaw.bindIndexed`, `OAI.MetricKMedian.SparseIntegerLaw.prod`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Compression_CircuitBitBound`, `KMedian_Compression_ComputedAffineKernel`, `KMedian_Compression_ComputedIntegerKernel`, `KMedian_Compression_ComputedPivot`, `KMedian_Geometry_BoundFreeCompression`, `KMedian_Process_BatchProposalProgram`, `KMedian_Programs_CardinalRoundProgram`, `KMedian_Rounding_RationalCopyTransition`, `KMedian_Sparse_SparseBind`, `KMedian_Sparse_SparseProduct`.
--
--   **Imports.** It imports the bundles `OAIQ035K014`, `OAIQ035K015`, `OAIQ035K017`, `OAIQ035K018` and `OAIQ035K019` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K039`, `OAIQ035K040`, `OAIQ035K041`, `OAIQ035K042`, `OAIQ035K043` and `OAIQ035K062`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K014
import Definitions.Def_OAIQ035K015
import Definitions.Def_OAIQ035K017
import Definitions.Def_OAIQ035K018
import Definitions.Def_OAIQ035K019

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_CircuitBitBound
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
-- module Solutions.OAIQ035_KM.KMedian_Compression_ComputedIntegerKernel
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
-- module Solutions.OAIQ035_KM.KMedian_Compression_ComputedAffineKernel
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
-- module Solutions.OAIQ035_KM.KMedian_Compression_ComputedPivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

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
-- module Solutions.OAIQ035_KM.KMedian_Geometry_BoundFreeCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

def compressionStepAuto {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℤ) (hsize : d+1 < μ.support.card) : IntegerLaw (Fin n) :=
  let z := computedAffineKernel μ v
  have hz : (∃ i, z i ≠ 0) ∧ (∑ i, z i=0) := by
    obtain ⟨L,hL⟩ := exists_feature_bound v
    have h := computedAffineKernel_spec μ v L hL hsize
    exact ⟨h.1,h.2.1⟩
  have hP := positiveSet_nonempty z hz.2 hz.1
  let p := computedPivot μ z hP
  have hp := computedPivot_spec μ z hP
  eliminateAt μ z p hp.1 hp.2 hz.2

def compressStepsAuto {n d : ℕ} (v : Fin n → Fin d → ℤ) :
    ℕ → IntegerLaw (Fin n) → IntegerLaw (Fin n)
  | 0,μ => μ
  | t+1,μ => if h : d+1 < μ.support.card then
      compressStepsAuto v t (compressionStepAuto μ v h) else μ

def compressAuto {n d : ℕ} (μ : IntegerLaw (Fin n)) (v : Fin n → Fin d → ℚ) :
    IntegerLaw (Fin n) :=
  compressStepsAuto (RationalLaw.scaledFeatures v) n μ

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.IntegerLaw
open Finset
variable {α β : Type} [Fintype α] [Fintype β]

def prod (μ : IntegerLaw α) (ν : IntegerLaw β) : IntegerLaw (α × β) where
  denominator := μ.denominator*ν.denominator
  denominator_pos := mul_pos μ.denominator_pos ν.denominator_pos
  numerator := fun a => μ.numerator a.1*ν.numerator a.2
  numerator_nonneg a := mul_nonneg (μ.numerator_nonneg _) (ν.numerator_nonneg _)
  total := by rw [Fintype.sum_prod_type]; simp only [← mul_sum,ν.total,← sum_mul,μ.total]

@[simp] theorem prod_weight (μ : IntegerLaw α) (ν : IntegerLaw β) (a : α) (b : β) :
    (μ.prod ν).rational.weight (a,b)=μ.rational.weight a*ν.rational.weight b := by
  simp only [prod,rational,Int.cast_mul]
  exact mul_div_mul_comm _ _ _ _

end MetricKMedian.IntegerLaw
namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β γ : Type}

def prod (μ : SparseIntegerLaw α) (ν : SparseIntegerLaw β) (f : α → β → γ) : SparseIntegerLaw γ where
  length := μ.length*ν.length
  states := Vector.ofFn (fun i => f μ.states[((finProdFinEquiv (m := μ.length) (n := ν.length)).symm i).1.val]
    ν.states[((finProdFinEquiv (m := μ.length) (n := ν.length)).symm i).2.val])
  law := (μ.law.prod ν.law).reindex (finProdFinEquiv (m := μ.length) (n := ν.length))

end MetricKMedian.SparseIntegerLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBind
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.RationalLaw
open Finset
variable {α : Type} {β : α → Type} [Fintype α] [∀ a, Fintype (β a)]

def sigma (μ : RationalLaw α) (κ : ∀ a, RationalLaw (β a)) : RationalLaw (Sigma β) where
  weight z := μ.weight z.1*(κ z.1).weight z.2
  nonneg z := mul_nonneg (μ.nonneg _) ((κ _).nonneg _)
  total := by
    rw [Fintype.sum_sigma]
    simp only [← mul_sum]
    calc
      _ = ∑ a, μ.weight a := sum_congr rfl (fun a _ => by rw [(κ a).total,mul_one])
      _ = 1 := μ.total

end MetricKMedian.RationalLaw
namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

def bindIndexed (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β) :
    SparseIntegerLaw β where
  length := ∑ a, (κ a).length
  states := Vector.ofFn (fun i => let z := finSigmaFinEquiv.symm i;
    (κ z.1).states[z.2.val])
  law := (μ.law.rational.sigma (fun a => (κ a).law.rational)).integer.reindex finSigmaFinEquiv

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_BatchProposalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.RationalBatchData.ProposalProgram
open Finset FixedBatch Binary Binary.PolyProgram
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
variable {C : Type} (I : C → Type) [∀ c, LinearOrder (I c)] [∀ c, Fintype (I c)]

variable {I}

def Input.enumActions (x : Input I) := enumeration (graph x.G) (heavySet (graphMass x.G x.g) x.b)
end MetricKMedian.RationalBatchData.ProposalProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_CardinalRoundProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseCardinalRounding.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse
abbrev br := encodeList encodeBool

end MetricKMedian.SparseCardinalRounding.Program
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

def erased (A : Finset (CopyState.Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graph G) H)) : Finset (CopyState.Copy (F := F) Δ) :=
  (Z.biUnion (heavy (graph G) H).erase).image Subtype.val

end MetricKMedian.RationalBatchData
end
end

end OAI
end


