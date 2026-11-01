-- Prove2me | Definitions.Def_OAIQ053K061
-- name    : OAIQ053K061
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:13:40.937257+00:00
-- url     : https://prove2.me/theorems/c31dba91-5b83-475d-9176-99e0b74c5a85
-- title:
--   Definitions bundle OAIQ053K061 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 28 declarations of OpenAI's Lean: 28 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Rounding_RationalSignedTerminal`, `KMedian_Sparse_SparseBernoulliSupport`, `KMedian_Sparse_SparseBundleEncoding`, `KMedian_Sparse_SparseBundleLaw`, `KMedian_Sparse_SparseCardinalFixed`, `KMedian_Sparse_SparseCardinalRounding`, `KMedian_Sparse_SparseCountFeatures`, `KMedian_Sparse_SparseCountRun`, `KMedian_Sparse_SparseGraphFeatures`, `KMedian_Sparse_SparseGraphRun`, `KMedian_Sparse_SparseGridRounding`, `KMedian_Sparse_SparseOuterCounts`, `KMedian_Sparse_SparseOuterLaw`, `KMedian_Sparse_SparseOuterReal`, `KMedian_Sparse_SparseSignedFixed`, `KMedian_Sparse_SparseSignedPreparation`, `KMedian_Sparse_SparseSignedRounding`.
--
--   **Imports.** It imports the bundles `OAIQ053K043`, `OAIQ053K049`, `OAIQ053K050`, `OAIQ053K051` and `OAIQ053K053` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K068` and `OAIQ053K069`; the proofs of `OAI.MetricKMedian.RationalPhysicalKernel.graph_data_all_s53` and `OAI.MetricKMedian.RationalPhysicalKernel.graph_data_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K043
import Definitions.Def_OAIQ053K049
import Definitions.Def_OAIQ053K050
import Definitions.Def_OAIQ053K051
import Definitions.Def_OAIQ053K053

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBernoulliSupport
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.RationalSignedTerminal.point_state _root_.OAI.MetricKMedian.SparseBernoulli.cast_flag _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

theorem pair_moment (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (i j : Fin n) (hij : i≠j) :
    (run (d := 2) p hp n).moment (fun q => flag q i*flag q j)=p i*p j := by
  simpa only [prod_pair hij] using subset_moment p hp {i,j} (by simp [hij] : ({i,j} : Finset (Fin n)).card ≤ 2)

end MetricKMedian.SparseBernoulli
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalSignedTerminal
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

theorem terminal_mean (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (i : Fin n) :
    (terminal u p hp).moment (fun q => point q i)=point p i := by
  rw [terminal,SparseIntegerLaw.map_moment]
  by_cases hi : u i<0
  · simp only [point_state,ite_eq_left hi,SparseIntegerLaw.moment_const]
  · simp only [point_state,ite_eq_right hi,SparseBernoulli.single_moment]

theorem terminal_pair (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (i j : Fin n) (hij : i≠j) :
    (terminal u p hp).moment (fun q => point q i*point q j)=point p i*point p j := by
  rw [terminal,SparseIntegerLaw.map_moment]
  by_cases hi : u i<0 <;> by_cases hj : u j<0
  · simp only [point_state,ite_eq_left hi,ite_eq_left hj,SparseIntegerLaw.moment_const]
  · simp only [point_state,ite_eq_left hi,ite_eq_right hj,SparseIntegerLaw.moment_mul,SparseBernoulli.single_moment]
  · simp only [point_state,ite_eq_right hi,ite_eq_left hj,SparseIntegerLaw.moment_mul_right,SparseBernoulli.single_moment]
  · simp only [point_state,ite_eq_right hi,ite_eq_right hj,SparseBernoulli.pair_moment _ _ _ _ hij]

end MetricKMedian.RationalSignedTerminal
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseCountFeatures
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseCounts
open Finset
variable {n m : ℕ}

theorem step_single (μ : SparseIntegerLaw (Table n m)) (ν : SparseIntegerLaw ((Fin n → ℕ)))
    (i j : Fin m) (h : Fin n) :
    (step μ ν i).moment (fun G => edge G h j)=
      if j=i then ν.moment (fun S => (S h:ℚ)) else μ.moment (fun G => edge G h j) := by
  have hh := (μ.prodCompress_spec ν (fun G S => next G S i) features).2.2
    (finSumFinEquiv (Sum.inl (finProdFinEquiv (h,j))))
  simp only [features_single] at hh
  refine hh.trans ?_
  by_cases hji : j=i
  · simp only [edge_next,ite_eq_left hji]
    exact μ.moment_const _
  · simp only [edge_next,ite_eq_right hji]
    simp only [SparseIntegerLaw.moment_const]

end MetricKMedian.SparseCounts
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseCountRun
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.SparseIntegerLaw.map_states _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseCounts
open Finset
variable {n m : ℕ}

theorem run_single (ν : Fin m → SparseIntegerLaw ((Fin n → ℕ)))
    (q : Fin n → Fin m → ℚ)
    (hq : ∀ h i, (ν i).moment (fun S => (S h:ℚ))=q h i)
    (t : ℕ) (ht : t ≤ m) (h : Fin n) (i : Fin m) :
    (run ν t).moment (fun G => edge G h i)=target q t h i := by
  induction t with
  | zero => simp [run,SparseIntegerLaw.dirac_moment,edge,target]
  | succ t ih =>
    have htm : t < m := by omega
    rw [run,dite_eq_left htm,step_single]
    by_cases hi : i=⟨t,htm⟩
    · subst i
      rw [ite_eq_left rfl,hq,target_succ_eq]
    · rw [ite_eq_right hi,ih (by omega),target_succ_ne q t htm h i hi]

theorem run_columns (ν : Fin m → SparseIntegerLaw ((Fin n → ℕ)))
    (P : Fin m → (Fin n → ℕ) → Prop)
    (hP : ∀ i, ∀ a : Fin (ν i).length, P i (ν i).states[a.val]) (t : ℕ) (ht : t ≤ m) :
    ∀ a : Fin (run ν t).length, ∀ i, i.val<t → P i ((run ν t).states[a.val] i) := by
  induction t with
  | zero => intro a i hi; omega
  | succ t ih =>
    have htm : t < m := by omega
    have he : run ν (t+1)=step (run ν t) (ν ⟨t,htm⟩) ⟨t,htm⟩ := by
      rw [run,dite_eq_left htm]
    let inv : SparseIntegerLaw (Table n m) → Prop := fun μ =>
      ∀ a : Fin μ.length, ∀ i, i.val<t+1 → P i (μ.states[a.val] i)
    change inv (run ν (t+1))
    rw [he]
    intro a i hi
    obtain ⟨j,k,hjk⟩ := ((run ν t).prodCompress_spec (ν ⟨t,htm⟩)
      (fun G S => next G S ⟨t,htm⟩) features).2.1 a
    change (step (run ν t) (ν ⟨t,htm⟩) ⟨t,htm⟩).states[a.val]=_ at hjk
    rw [hjk]
    by_cases hi' : i=⟨t,htm⟩
    · subst i
      simpa only [next,Function.update_self] using hP ⟨t,htm⟩ k
    · have hiv : i.val≠t := fun h => hi' (Fin.ext h)
      simpa only [next,Function.update_of_ne hi'] using ih (by omega) j i (by omega)

end MetricKMedian.SparseCounts
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseCardinalRounding
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.RationalSignedTerminal.point_state _root_.OAI.MetricKMedian.SparseIntegerLaw.map_states _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect _root_.OAI.MetricKMedian.SparseTargetSubset.point_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseCardinalRounding
open Finset RationalWeightedStep
variable {n : ℕ}

theorem round_invariants (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (K : ℕ)
    (hs : (∑ i, point p i)=(K:ℚ)) :
    ∀ a : Fin (round p).length,
      (∀ i, point (round p).states[a.val] i=0 ∨ point (round p).states[a.val] i=1) ∧
      (∑ i, point (round p).states[a.val] i)=(K:ℚ) := by
  intro a
  obtain ⟨h0,h1,h2⟩ := SparseWeightedPartial.run_invariants (fun _ => 1)
    (fun _ => by norm_num) p hp n a
  simp only [one_mul] at h1
  have hsum : (∑ i, point (round p).states[a.val] i)=(K:ℚ) := h1.trans hs
  exact ⟨integral_of_small_fractional _ h0 K hsum (by simpa only [round, Nat.sub_self, max_eq_right (Nat.zero_le 1)] using h2),hsum⟩

end MetricKMedian.SparseCardinalRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseCardinalFixed
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.RationalSignedTerminal.point_state _root_.OAI.MetricKMedian.SparseIntegerLaw.map_states _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect _root_.OAI.MetricKMedian.SparseTargetSubset.point_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.SparseCardinalRounding
open RationalWeightedStep

theorem zero_fixed {n : ℕ} (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (i : Fin n) (hi : point p i=0)
    (a : Fin (round p).length) : point (round p).states[a.val] i=0 := by
  apply SparseIntegerLaw.zero_nonnegative (round p) (fun q => point q i)
    (fun b => ((SparseWeightedPartial.run_invariants (fun _ => 1)
      (fun _ => by norm_num) p hp n b).1 i).1)
    ((round_mean p i).trans hi) a
    (SparseWeightedPartial.run_positive _ _ _ _ a)

end MetricKMedian.SparseCardinalRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseGridRounding
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.RationalSignedTerminal.point_state _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect _root_.OAI.MetricKMedian.SparseTargetSubset.point_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseGridRounding
open Finset
open RationalWeightedStep (point)
variable {n : ℕ}

theorem law_invariants (q : Fin n → ℚ) (K L : ℕ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ L) (hs : (∑ i, q i)=(K:ℚ)) :
    ∀ a : Fin (law q).length,
      (∑ i, (law q).states[a.val] i)=K ∧
      (∀ i, (law q).states[a.val] i ≤ L) ∧
      (∀ i, (law q).states[a.val] i=base q i ∨ (law q).states[a.val] i=base q i+1) := by
  intro a
  change Fin (SparseCardinalRounding.round (fraction q)).length at a
  have he := SparseIntegerLaw.map_states (SparseCardinalRounding.round (fraction q)) (count q) a
  change (law q).states[a.val]=_ at he
  rw [he]
  have hh := SparseCardinalRounding.round_invariants (fraction q) (fraction_unit q (fun i => (hq i).1))
    (K-∑ i,base q i) (fraction_sum q (fun i => (hq i).1) K hs) a
  refine ⟨?_,?_,?_⟩
  · have heq : (∑ i, (count q (SparseCardinalRounding.round (fraction q)).states[a.val] i:ℚ))=(K:ℚ) := by
      simp only [count_cast _ _ hh.1,sum_add_distrib,hh.2,
        Nat.cast_sub (base_sum_le q (fun i => (hq i).1) K hs),Nat.cast_sum]
      ring
    exact_mod_cast heq
  · intro i
    have hb : base q i ≤ L := by exact_mod_cast (Nat.floor_le (hq i).1).trans (hq i).2
    by_cases hi : point (SparseCardinalRounding.round (fraction q)).states[a.val] i=1
    · have hl : base q i < L := by
        by_contra hn
        have heq : base q i=L := le_antisymm hb (le_of_not_gt hn)
        have hz : point (fraction q) i=0 := by
          simp only [fraction,point,Vector.getElem_ofFn]
          have hh := Nat.floor_le (hq i).1
          change (base q i:ℚ) ≤ q i at hh
          have hh' := (hq i).2
          rw [heq] at hh ⊢
          linarith only [hh,hh']
        have hfixed := SparseCardinalRounding.zero_fixed (fraction q)
          (fraction_unit q (fun i => (hq i).1)) i hz a
        rw [hi] at hfixed
        norm_num at hfixed
      simpa only [count,ite_eq_left hi] using Nat.add_one_le_iff.mpr hl
    · simpa only [count,ite_eq_right hi,Nat.add_zero] using hb
  · intro i
    unfold count
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl (Nat.add_zero _)

theorem law_mean (q : Fin n → ℚ) (K : ℕ) (hq : ∀ i, 0 ≤ q i)
    (hs : (∑ i,q i)=(K:ℚ)) (i : Fin n) :
    (law q).moment (fun c => (c i:ℚ))=q i := by
  rw [law,SparseIntegerLaw.map_moment]
  calc
    _ = (SparseCardinalRounding.round (fraction q)).moment
        (fun p => (base q i:ℚ)+point p i) := by
      apply SparseIntegerLaw.moment_congr
      intro a
      exact count_cast _ _ (SparseCardinalRounding.round_invariants (fraction q)
        (fraction_unit q hq) (K-∑ i,base q i) (fraction_sum q hq K hs) a).1 i
    _ = q i := by
      rw [SparseIntegerLaw.moment_add,SparseIntegerLaw.moment_const,SparseCardinalRounding.round_mean]
      simp only [fraction,point,Vector.getElem_ofFn,add_sub_cancel]

end MetricKMedian.SparseGridRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBundleLaw
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseBundles
open Finset
variable {n m : ℕ}

theorem single (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ)
    (hq : ∀ i j, 0 ≤ q i j) (hs : ∀ j, (∑ i,q i j)=(K j:ℚ)) (i : Fin n) (j : Fin m) :
    (law q).moment (fun G => (G j i:ℚ))=q i j := by
  have hh := SparseCounts.run_single (fun j => SparseGridRounding.law (fun i => q i j)) q
    (fun i j => SparseGridRounding.law_mean (fun i => q i j) (K j) (fun i => hq i j) (hs j) i)
    m le_rfl i j
  simpa only [SparseCounts.target,SparseCounts.edge,ite_eq_left j.isLt] using hh

theorem invariants (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ) (L : ℕ)
    (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ L) (hs : ∀ j, (∑ i,q i j)=(K j:ℚ)) :
    ∀ a : Fin (law q).length, ∀ j,
      (∑ i,(law q).states[a.val] j i)=K j ∧
      (∀ i,(law q).states[a.val] j i ≤ L) ∧
      (∀ i,(law q).states[a.val] j i=SparseGridRounding.base (fun i => q i j) i ∨
        (law q).states[a.val] j i=SparseGridRounding.base (fun i => q i j) i+1) := by
  intro a j
  exact SparseCounts.run_columns (fun j => SparseGridRounding.law (fun i => q i j))
    (fun j S => (∑ i,S i)=K j ∧ (∀ i,S i ≤ L) ∧
      (∀ i,S i=SparseGridRounding.base (fun i => q i j) i ∨
        S i=SparseGridRounding.base (fun i => q i j) i+1))
    (fun j => SparseGridRounding.law_invariants (fun i => q i j) (K j) L (fun i => hq i j) (hs j))
    m le_rfl a j j.isLt

end MetricKMedian.SparseBundles
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBundleEncoding
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseBundleEncoding
open Finset
variable {n m : ℕ}

theorem expectation (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ) (L : ℕ)
    (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ L) (hs : ∀ j, (∑ i, q i j) = (K j : ℚ))
    (v : SparseCounts.Table n m → ℝ) :
    (law q).expect (fun ξ => v (decode q ξ)) =
      (SparseBundles.law q).realIndex.expect (fun a => v (SparseBundles.law q).states[a.val]) := by
  rw [law, FiniteLaw.expect_map]
  congr 1
  funext a
  rw [decode_encode q _ (fun j => (SparseBundles.invariants q K L hq hs a j).2.2)]

theorem support (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ) (L : ℕ)
    (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ L) (hs : ∀ j, (∑ i, q i j) = (K j : ℚ))
    (ξ : Fin m → Finset (Fin n)) (hξ : 0 < (law q).weight ξ) :
    ∃ a : Fin (SparseBundles.law q).length,
      0 < (SparseBundles.law q).realIndex.weight a ∧
      decode q ξ = (SparseBundles.law q).states[a.val] := by
  obtain ⟨a, ha, rfl⟩ := FiniteLaw.support_map _ _ ξ hξ
  exact ⟨a, ha, decode_encode q _ (fun j => (SparseBundles.invariants q K L hq hs a j).2.2)⟩

theorem mean (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ) (L : ℕ)
    (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ L) (hs : ∀ j, (∑ i, q i j) = (K j : ℚ))
    (i : Fin n) (j : Fin m) :
    (law q).expect (fun ξ => (decode q ξ j i : ℝ)) = (q i j : ℝ) := by
  rw [expectation q K L hq hs (fun G => (G j i : ℝ))]
  exact ((SparseBundles.law q).realIndex_expect (fun G => (G j i : ℚ))).trans
    (congrArg (fun x : ℚ => (x : ℝ)) (SparseBundles.single q K (fun i j => (hq i j).1) hs i j))

end MetricKMedian.SparseBundleEncoding

namespace MetricKMedian.SparseRescaledInner
open Finset
variable {n t : ℕ}

theorem encoded_mean (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ)
    (p : Fin t → ℚ) (K : Fin t → ℕ) (Δ : ℕ) (g : ℝ)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ j, 0 < p j) (hm : ∀ j, ∑ i ∈ P j, y i = p j)
    (hK : ∀ j, K j ≤ Δ) (j : Fin t) (i : Fin n) :
    (encodedLaw P y p K).expect (fun ξ => g * (encodedCount P y p K ξ (j,i) : ℝ)) =
      if i ∈ P j then (g * (K j : ℝ)) * (y i : ℝ) / (p j : ℝ) else 0 := by
  rw [FiniteLaw.expect_mul]
  have h := SparseBundleEncoding.mean (piece P y p K) K Δ
    (fun i j => ⟨piece_nonnegative P y p K hy hp i j, piece_cap P y p K Δ hy hp hm hK i j⟩)
    (piece_sum P y p K hp hm) i j
  change (encodedLaw P y p K).expect (fun ξ => (encodedCount P y p K ξ (j,i) : ℝ)) = _ at h
  rw [h, cast_scaled_piece]

end MetricKMedian.SparseRescaledInner
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseGraphFeatures
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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

theorem step_single (μ : SparseIntegerLaw (Graph n m)) (ν : SparseIntegerLaw (Finset (Fin n)))
    (i j : Fin m) (h : Fin n) :
    (step μ ν i).moment (fun G => edge G h j)=
      if j=i then ν.moment (fun S => if h∈S then 1 else 0) else μ.moment (fun G => edge G h j) := by
  have hh := (μ.prodCompress_spec ν (fun G S => next G S i) features).2.2
    (finSumFinEquiv (Sum.inl (finProdFinEquiv (h,j))))
  simp only [features_single] at hh
  refine hh.trans ?_
  by_cases hji : j=i
  · simp only [edge_next,ite_eq_left hji]
    exact μ.moment_const _
  · simp only [edge_next,ite_eq_right hji]
    simp only [SparseIntegerLaw.moment_const]

theorem step_pair (μ : SparseIntegerLaw (Graph n m)) (ν : SparseIntegerLaw (Finset (Fin n)))
    (i j k : Fin m) (h l : Fin n) (hjk : j≠k) :
    (step μ ν i).moment (fun G => edge G h j*edge G l k)=
      if j=i then ν.moment (fun S => if h∈S then 1 else 0)*μ.moment (fun G => edge G l k)
      else if k=i then μ.moment (fun G => edge G h j)*ν.moment (fun S => if l∈S then 1 else 0)
      else μ.moment (fun G => edge G h j*edge G l k) := by
  have hh := (μ.prodCompress_spec ν (fun G S => next G S i) features).2.2
    (finSumFinEquiv (Sum.inr (finProdFinEquiv (finProdFinEquiv (h,j),finProdFinEquiv (l,k)))))
  simp only [features_pair] at hh
  refine hh.trans ?_
  by_cases hji : j=i
  · have hki : k≠i := fun hk => hjk (hji.trans hk.symm)
    simp only [edge_next,ite_eq_left hji,ite_eq_right hki,
      SparseIntegerLaw.moment_mul_right,SparseIntegerLaw.moment_mul]
  · by_cases hki : k=i
    · simp only [edge_next,ite_eq_right hji,ite_eq_left hki,
        SparseIntegerLaw.moment_mul,SparseIntegerLaw.moment_mul_right]
    · simp only [edge_next,ite_eq_right hji,ite_eq_right hki,SparseIntegerLaw.moment_const]

end MetricKMedian.SparseGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseGraphRun
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.SparseEnumeratedGraph.mem_lift _root_.OAI.MetricKMedian.SparseGraph.cast_edge _root_.OAI.MetricKMedian.SparseIntegerLaw.map_states _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
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

theorem run_single (ν : Fin m → SparseIntegerLaw (Finset (Fin n)))
    (q : Fin n → Fin m → ℚ)
    (hq : ∀ h i, (ν i).moment (fun S => if h∈S then 1 else 0)=q h i)
    (t : ℕ) (ht : t ≤ m) (h : Fin n) (i : Fin m) :
    (run ν t).moment (fun G => edge G h i)=target q t h i := by
  induction t with
  | zero => simp [run,SparseIntegerLaw.dirac_moment,edge,target]
  | succ t ih =>
    have htm : t < m := by omega
    rw [run,dite_eq_left htm,step_single]
    by_cases hi : i=⟨t,htm⟩
    · subst i
      rw [ite_eq_left rfl,hq,target_succ_eq]
    · rw [ite_eq_right hi,ih (by omega),target_succ_ne q t htm h i hi]

theorem run_pair (ν : Fin m → SparseIntegerLaw (Finset (Fin n)))
    (q : Fin n → Fin m → ℚ)
    (hq : ∀ h i, (ν i).moment (fun S => if h∈S then 1 else 0)=q h i)
    (t : ℕ) (ht : t ≤ m) (h l : Fin n) (i j : Fin m) (hij : i≠j) :
    (run ν t).moment (fun G => edge G h i*edge G l j)=target q t h i*target q t l j := by
  induction t with
  | zero => simp [run,SparseIntegerLaw.dirac_moment,edge,target]
  | succ t ih =>
    have htm : t < m := by omega
    rw [run,dite_eq_left htm,step_pair _ _ _ _ _ _ _ hij]
    by_cases hi : i=⟨t,htm⟩
    · have hj : j≠⟨t,htm⟩ := fun he => hij (hi.trans he.symm)
      rw [ite_eq_left hi,hq,run_single ν q hq t (by omega),
        target_succ_ne q t htm l j hj]
      subst i
      rw [target_succ_eq]
    · rw [ite_eq_right hi]
      by_cases hj : j=⟨t,htm⟩
      · rw [ite_eq_left hj,hq,run_single ν q hq t (by omega),target_succ_ne q t htm h i hi]
        subst j
        rw [target_succ_eq]
      · rw [ite_eq_right hj,ih (by omega),target_succ_ne q t htm h i hi,
          target_succ_ne q t htm l j hj]

end MetricKMedian.SparseGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSignedRounding
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedRounding
open Finset
open RationalWeightedStep (point fractional)
open SparseWeightedPartial (features features_single features_pair)
variable {n : ℕ}

theorem round_mean (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (i : Fin n) :
    (round u p hp).moment (fun q => point q i)=point p i := by
  have hh := ((SparseSignedPartial.run u p n).bindCompress_spec (kernel u p hp)
    features).2.2 (finSumFinEquiv (Sum.inl i))
  simp only [features_single,kernel,RationalSignedTerminal.terminal_mean] at hh
  exact hh.trans (SparseSignedPartial.run_mean u p n i)

theorem round_pair (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (i j : Fin n) (hij : i ≠ j) :
    (round u p hp).moment (fun q => point q i*point q j) ≤ point p i*point p j := by
  have hh := ((SparseSignedPartial.run u p n).bindCompress_spec (kernel u p hp)
    features).2.2 (finSumFinEquiv (Sum.inr (finProdFinEquiv (i,j))))
  simp only [features_pair,kernel,RationalSignedTerminal.terminal_pair _ _ _ _ _ hij] at hh
  exact hh.trans_le (SparseSignedPartial.run_pair u p n i j hij)

end MetricKMedian.SparseSignedRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSignedPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedPreparation
open Finset
open RationalWeightedStep (point fractional)
variable {n m : ℕ}

theorem kernel_nominal_pair (D : Fin m → Finset (Fin n)) (q : Vector ℚ m)
    (hq : ∀ e, 0 ≤ point q e ∧ point q e ≤ 1) (e f : Fin m) (hef : e≠f) :
    (kernel D q hq).moment (fun z => SparseBernoulli.flag z.2.2 e*SparseBernoulli.flag z.2.2 f)=
      point q e*point q f := by
  rw [kernel,SparseIntegerLaw.prod_moment]
  simp only [SparseBernoulli.pair_moment _ _ _ _ hef,SparseIntegerLaw.moment_const]

theorem nominal_pair (D : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (p : Vector ℚ m)
    (hp : ∀ e, 0 ≤ point p e ∧ point p e ≤ 1) (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1)
    (e f : Fin m) (hef : e≠f) :
    (law D c p hp hc).moment (fun z => SparseBernoulli.flag z.2.2 e*SparseBernoulli.flag z.2.2 f) ≤
      point p e*point p f := by
  rw [law,SparseIntegerLaw.bindIndexed_moment]
  simp only [kernel_nominal_pair _ _ _ _ _ hef]
  exact SparseSignedRounding.round_pair _ _ _ _ _ hef

end MetricKMedian.SparseSignedPreparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseOuterLaw
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open RationalWeightedStep (point)
open SparseGridRounding (base fraction)
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem activation_adjacent (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e)
    (a : Fin (law D c q hc hq).length) (e : Fin m) (i : Fin n) :
    let b : ℚ := if i∈D e then (base q e:ℚ) else 0
    activation D q (law D c q hc hq).states[a.val] e i=b ∨
      activation D q (law D c q hc hq).states[a.val] e i=b+1 := by
  dsimp only [activation]
  split_ifs
  all_goals first | exact Or.inl (add_zero _) | exact Or.inr rfl

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSignedFixed
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedRounding
open Finset
open RationalWeightedStep (point fractional)
open SparseWeightedPartial (features)
variable {n : ℕ}

theorem fixed (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1)
    (hu : ∀ i, 0 < u i → u i ≤ 1) (e : Fin n)
    (he : point p e=0 ∨ point p e=1) (a : Fin (round u p hp).length) :
    point (round u p hp).states[a.val] e=point p e := by
  rcases he with he | he
  · rw [he]
    apply SparseIntegerLaw.zero_nonnegative (round u p hp) (fun q => point q e)
      (fun i => ((round_invariants u p hp hu i).1 e).1)
      ((round_mean u p hp e).trans he) a (positive u p hp a)
  · have hh : (round u p hp).moment (fun q => 1-point q e)=0 := by
      rw [SparseIntegerLaw.moment_sub,SparseIntegerLaw.moment_const,round_mean,he,sub_self]
    have hz := SparseIntegerLaw.zero_nonnegative (round u p hp) (fun q => 1-point q e)
      (fun i => sub_nonneg.mpr ((round_invariants u p hp hu i).1 e).2)
      hh a (positive u p hp a)
    rw [he]
    linarith only [hz]

end MetricKMedian.SparseSignedRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseOuterCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open RationalWeightedStep (point)
open SparseGridRounding (base fraction)
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem point_fixed (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (e : Fin m)
    (he : point (fraction q) e=0) : ∀ a : Fin (law D c q hc hq).length,
      point (law D c q hc hq).states[a.val].1 e=0 := by
  unfold law SparseSignedPreparation.law
  dsimp only
  apply SparseIntegerLaw.bindIndexed_property _ _ (fun z : State n m => point z.1 e=0)
  intro a
  unfold SparseSignedPreparation.kernel
  apply SparseIntegerLaw.prod_property _ _ _ (fun z : State n m => point z.1 e=0)
  intro b d
  exact (SparseSignedRounding.fixed (SparseSignedPreparation.signed D c) (fraction q)
    (SparseGridRounding.fraction_unit q hq)
    (fun j _ => (sub_le_self _ (Nat.cast_nonneg _)).trans (hc j).2) e (Or.inl he) a).trans he

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseOuterReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseOuterLaw
open Finset
open RationalWeightedStep (point)
open SparseGridRounding (base fraction)
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem outsideCount_le_at (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ)
    (hc : ∀ e, 0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e, 0 ≤ q e) (L : ℕ)
    (a : Fin (law D c q hc hq).length) (e : Fin m) (hL : q e ≤ L) :
    outsideCount q (law D c q hc hq).states[a.val] e ≤ L := by
  have hb : base q e ≤ L := by exact_mod_cast (Nat.floor_le (hq e)).trans hL
  by_cases hi : 0 < point (law D c q hc hq).states[a.val].1 e
  · have hl : base q e < L := by
      by_contra hn
      have heq : base q e = L := le_antisymm hb (le_of_not_gt hn)
      have hz : point (fraction q) e = 0 := by
        simp only [fraction, point, Vector.getElem_ofFn]
        have hh := Nat.floor_le (hq e)
        change (base q e : ℚ) ≤ q e at hh
        rw [heq] at hh ⊢
        linarith only [hh, hL]
      have hf := point_fixed D c q hc hq e hz a
      rw [hf] at hi
      exact (lt_irrefl 0) hi
    simpa only [outsideCount, ite_eq_left hi] using Nat.add_one_le_iff.mpr hl
  · simpa only [outsideCount, ite_eq_right hi, Nat.add_zero] using hb

end MetricKMedian.SparseOuterLaw
end

end OAI
end


