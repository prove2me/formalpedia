-- Prove2me | Definitions.Def_OAIQ053K069
-- name    : OAIQ053K069
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:18:00.182045+00:00
-- url     : https://prove2.me/theorems/61c7782f-1669-49d4-b607-eb7f5f9d638c
-- title:
--   Definitions bundle OAIQ053K069 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 14 declarations of OpenAI's Lean: 14 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedian_Sparse_SparseBundleEncoding`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseBundleEncoding.lean), [`KMedian_Sparse_SparseBundleLaw`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseBundleLaw.lean), [`KMedian_Sparse_SparseCountRun`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseCountRun.lean), [`KMedian_Sparse_SparseGridRounding`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseGridRounding.lean), [`KMedian_Sparse_SparseGridZero`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseGridZero.lean), [`KMedian_Sparse_SparsePreparedBudget`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparsePreparedBudget.lean), [`KMedian_Sparse_SparseRescaledInner`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseRescaledInner.lean).
--
--   **Imports.** It imports the bundles `OAIQ053K060`, `OAIQ053K061` and `OAIQ053K062` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ053K074`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K060
import Definitions.Def_OAIQ053K061
import Definitions.Def_OAIQ053K062

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

theorem run_pair (ν : Fin m → SparseIntegerLaw ((Fin n → ℕ)))
    (q : Fin n → Fin m → ℚ)
    (hq : ∀ h i, (ν i).moment (fun S => (S h:ℚ))=q h i)
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

end MetricKMedian.SparseCounts
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseGridRounding
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

theorem law_pair (q : Fin n → ℚ) (K : ℕ) (hq : ∀ i, 0 ≤ q i)
    (hs : (∑ i,q i)=(K:ℚ)) (i j : Fin n) (hij : i≠j) :
    (law q).moment (fun c => (c i:ℚ)*(c j:ℚ)) ≤ q i*q j := by
  rw [law,SparseIntegerLaw.map_moment]
  calc
    _ = (SparseCardinalRounding.round (fraction q)).moment
        (fun p => ((base q i:ℚ)+point p i)*((base q j:ℚ)+point p j)) := by
      apply SparseIntegerLaw.moment_congr
      intro a
      have hh := SparseCardinalRounding.round_invariants (fraction q)
        (fraction_unit q hq) (K-∑ i,base q i) (fraction_sum q hq K hs) a
      rw [count_cast _ _ hh.1,count_cast _ _ hh.1]
    _ ≤ ((base q i:ℚ)+point (fraction q) i)*((base q j:ℚ)+point (fraction q) j) :=
      SparseIntegerLaw.moment_affine_pair_le _ _ _ _ _ _ _
        (SparseCardinalRounding.round_mean _ i) (SparseCardinalRounding.round_mean _ j)
        (SparseCardinalRounding.round_pair _ i j hij)
    _ = q i*q j := by simp only [fraction,point,Vector.getElem_ofFn,add_sub_cancel]

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

theorem cross_pair (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ)
    (hq : ∀ i j, 0 ≤ q i j) (hs : ∀ j, (∑ i,q i j)=(K j:ℚ))
    (i h : Fin n) (j k : Fin m) (hjk : j≠k) :
    (law q).moment (fun G => (G j i:ℚ)*(G k h:ℚ))=q i j*q h k := by
  have hh := SparseCounts.run_pair (fun j => SparseGridRounding.law (fun i => q i j)) q
    (fun i j => SparseGridRounding.law_mean (fun i => q i j) (K j) (fun i => hq i j) (hs j) i)
    m le_rfl i h j k hjk
  simpa only [SparseCounts.target,SparseCounts.edge,ite_eq_left j.isLt,ite_eq_left k.isLt] using hh

theorem same_pair (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ)
    (hq : ∀ i j, 0 ≤ q i j) (hs : ∀ j, (∑ i,q i j)=(K j:ℚ))
    (i h : Fin n) (j : Fin m) (hih : i≠h) :
    (law q).moment (fun G => (G j i:ℚ)*(G j h:ℚ)) ≤ q i j*q h j := by
  have hh := SparseCounts.run_same (fun j => SparseGridRounding.law (fun i => q i j)) m le_rfl i h j
  simp only [SparseCounts.edge,ite_eq_left j.isLt] at hh
  exact hh.trans_le (SparseGridRounding.law_pair (fun i => q i j) (K j)
    (fun i => hq i j) (hs j) i h hih)

theorem variance (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ) (L : ℕ)
    (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ L) (hs : ∀ j, (∑ i,q i j)=(K j:ℚ))
    (i : Fin n) (j : Fin m) :
    (law q).realIndex.variance (fun a => ((law q).states[a.val] j i:ℝ)) ≤ (q i j:ℝ) := by
  apply FiniteLaw.adjacent_variance _ _
    (m := SparseGridRounding.base (fun i => q i j) i) (Nat.cast_nonneg _) ?_ ?_
  · intro a _
    rcases (invariants q K L hq hs a j).2.2 i with hh | hh
    · exact Or.inl (by exact_mod_cast hh)
    · exact Or.inr (by exact_mod_cast hh)
  · have hh := (law q).realIndex_expect (fun G => (G j i:ℚ))
    simp only [Rat.cast_natCast] at hh
    rw [hh,single q K (fun i j => (hq i j).1) hs]

end MetricKMedian.SparseBundles
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseGridZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseGridRounding
open RationalWeightedStep (point)
variable {n : ℕ}

theorem zero (q : Fin n → ℚ) (hq : ∀ i, 0 ≤ q i) (i : Fin n) (hi : q i=0)
    (a : Fin (law q).length) : (law q).states[a.val] i=0 := by
  have hb : base q i=0 := by simp only [base,hi,Nat.floor_zero]
  have hf : point (fraction q) i=0 := by
    simp only [fraction,point,Vector.getElem_ofFn,hi,hb,Nat.cast_zero,sub_zero]
  change Fin (SparseCardinalRounding.round (fraction q)).length at a
  have hz := SparseCardinalRounding.zero_fixed (fraction q) (fraction_unit q hq) i hf a
  have he := SparseIntegerLaw.map_states (SparseCardinalRounding.round (fraction q)) (count q) a
  change (law q).states[a.val]=_ at he
  rw [he]
  simp only [count,hz,zero_ne_one,ite_false,hb,Nat.add_zero]

end MetricKMedian.SparseGridRounding

namespace MetricKMedian.SparseBundles
variable {n m : ℕ}

theorem zero (q : Fin n → Fin m → ℚ) (hq : ∀ i j, 0 ≤ q i j)
    (a : Fin (law q).length) (i : Fin n) (j : Fin m) (hi : q i j=0) :
    (law q).states[a.val] j i=0 := by
  have hh := SparseCounts.run_columns (fun j => SparseGridRounding.law (fun i => q i j))
    (fun j S => ∀ i,q i j=0 → S i=0)
    (fun j a i hi => SparseGridRounding.zero (fun i => q i j) (fun i => hq i j) i hi a)
    m le_rfl a j j.isLt
  exact hh i hi

end MetricKMedian.SparseBundles
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseRescaledInner
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseRescaledInner
open Finset
variable {n t : ℕ}

theorem invariants (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ) (p : Fin t → ℚ)
    (K : Fin t → ℕ) (Δ : ℕ) (hy : ∀ i,0 ≤ y i) (hp : ∀ j,0 < p j)
    (hm : ∀ j,∑ i∈P j,y i=p j) (hK : ∀ j,K j ≤ Δ) :
    ∀ a : Fin (law P y p K).length,∀ j,
      (∑ i,(law P y p K).states[a.val] j i)=K j ∧
      (∀ i,(law P y p K).states[a.val] j i ≤ Δ) ∧
      (∀ i,i∉P j → (law P y p K).states[a.val] j i=0) := by
  intro a j
  have hq : ∀ i j,0 ≤ piece P y p K i j ∧ piece P y p K i j ≤ Δ := fun i j => ⟨piece_nonnegative P y p K hy hp i j,piece_cap P y p K Δ hy hp hm hK i j⟩
  have hh := SparseBundles.invariants (piece P y p K) K Δ hq (piece_sum P y p K hp hm) a j
  refine ⟨hh.1,hh.2.1,?_⟩
  intro i hi
  exact SparseBundles.zero (piece P y p K) (piece_nonnegative P y p K hy hp) a i j
    (by simp only [piece,ite_eq_right hi])

end MetricKMedian.SparseRescaledInner
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

theorem pair (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ) (L : ℕ)
    (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ L) (hs : ∀ j, (∑ i, q i j) = (K j : ℚ))
    (i h : Fin n) (j k : Fin m) (hh : i ≠ h ∨ j ≠ k) :
    (law q).expect (fun ξ => (decode q ξ j i : ℝ) * (decode q ξ k h : ℝ)) ≤
      (q i j : ℝ) * (q h k : ℝ) := by
  rw [expectation q K L hq hs (fun G => (G j i : ℝ) * (G k h : ℝ))]
  have he := (SparseBundles.law q).realIndex_expect (fun G => (G j i : ℚ) * (G k h : ℚ))
  simp only [Rat.cast_mul, Rat.cast_natCast] at he
  rw [he, ← Rat.cast_mul]
  apply Rat.cast_le.mpr
  by_cases hjk : j = k
  · subst k
    exact SparseBundles.same_pair q K (fun i j => (hq i j).1) hs i h j
      (hh.resolve_right (not_not.mpr rfl))
  · exact (SparseBundles.cross_pair q K (fun i j => (hq i j).1) hs i h j k hjk).le

theorem variance (q : Fin n → Fin m → ℚ) (K : Fin m → ℕ) (L : ℕ)
    (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ L) (hs : ∀ j, (∑ i, q i j) = (K j : ℚ))
    (i : Fin n) (j : Fin m) :
    (law q).variance (fun ξ => (decode q ξ j i : ℝ)) ≤ (q i j : ℝ) := by
  have hv := SparseBundles.variance q K L hq hs i j
  rw [FiniteLaw.variance_eq] at hv ⊢
  rw [expectation q K L hq hs (fun G => (G j i : ℝ)^2),
    expectation q K L hq hs (fun G => (G j i : ℝ))]
  exact hv

end MetricKMedian.SparseBundleEncoding

namespace MetricKMedian.SparseRescaledInner
open Finset
variable {n t : ℕ}

theorem encoded_pieces (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ)
    (p : Fin t → ℚ) (K : Fin t → ℕ) (Δ : ℕ)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ j, 0 < p j) (hm : ∀ j, ∑ i ∈ P j, y i = p j)
    (hK : ∀ j, K j ≤ Δ) (ξ : Fin t → Finset (Fin n))
    (hξ : 0 < (encodedLaw P y p K).weight ξ) : ∀ j,
      (∑ i, encodedCount P y p K ξ (j,i)) = K j ∧
      (∀ i, encodedCount P y p K ξ (j,i) ≤ Δ) ∧
      (∀ i, i ∉ P j → encodedCount P y p K ξ (j,i) = 0) := by
  obtain ⟨a, _, ha⟩ := SparseBundleEncoding.support (piece P y p K) K Δ
    (fun i j => ⟨piece_nonnegative P y p K hy hp i j, piece_cap P y p K Δ hy hp hm hK i j⟩)
    (piece_sum P y p K hp hm) ξ hξ
  simp only [encodedCount, ha]
  exact invariants P y p K Δ hy hp hm hK a

theorem encoded_pair (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ)
    (p : Fin t → ℚ) (K : Fin t → ℕ) (Δ : ℕ) (g : ℝ)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ j, 0 < p j) (hm : ∀ j, ∑ i ∈ P j, y i = p j)
    (hK : ∀ j, K j ≤ Δ) (a b : Fin t × Fin n) (hab : a ≠ b) :
    (encodedLaw P y p K).expect (fun ξ =>
      (g * (encodedCount P y p K ξ a : ℝ)) * (g * (encodedCount P y p K ξ b : ℝ))) ≤
      (if a.2 ∈ P a.1 then (g * (K a.1 : ℝ)) * (y a.2 : ℝ) / (p a.1 : ℝ) else 0) *
      (if b.2 ∈ P b.1 then (g * (K b.1 : ℝ)) * (y b.2 : ℝ) / (p b.1 : ℝ) else 0) := by
  have hne : a.2 ≠ b.2 ∨ a.1 ≠ b.1 := by
    by_contra h
    push Not at h
    exact hab (Prod.ext h.2 h.1)
  have hh := SparseBundleEncoding.pair (piece P y p K) K Δ
    (fun i j => ⟨piece_nonnegative P y p K hy hp i j, piece_cap P y p K Δ hy hp hm hK i j⟩)
    (piece_sum P y p K hp hm) a.2 b.2 a.1 b.1 hne
  have hf : ∀ x y : ℝ, (g*x)*(g*y) = g^2*(x*y) := by intros; ring
  rw [← cast_scaled_piece, ← cast_scaled_piece, hf]
  simp only [hf, FiniteLaw.expect_mul]
  exact mul_le_mul_of_nonneg_left hh (sq_nonneg g)

theorem encoded_variance (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ)
    (p : Fin t → ℚ) (K : Fin t → ℕ) (Δ : ℕ) (g : ℝ)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ j, 0 < p j) (hm : ∀ j, ∑ i ∈ P j, y i = p j)
    (hK : ∀ j, K j ≤ Δ) (a : Fin t × Fin n) :
    (encodedLaw P y p K).variance (fun ξ => g * (encodedCount P y p K ξ a : ℝ)) ≤
      g * (if a.2 ∈ P a.1 then (g * (K a.1 : ℝ)) * (y a.2 : ℝ) / (p a.1 : ℝ) else 0) := by
  have hh := SparseBundleEncoding.variance (piece P y p K) K Δ
    (fun i j => ⟨piece_nonnegative P y p K hy hp i j, piece_cap P y p K Δ hy hp hm hK i j⟩)
    (piece_sum P y p K hp hm) a.2 a.1
  change (encodedLaw P y p K).variance (fun ξ => (encodedCount P y p K ξ a : ℝ)) ≤ _ at hh
  rw [← cast_scaled_piece, FiniteLaw.variance_mul]
  simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_left hh (sq_nonneg g)

end MetricKMedian.SparseRescaledInner
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparsePreparedBudget
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw SparseGridRounding
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem opening_le (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (Δ : ℕ)
    (hc : ∀ e,0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e,0 ≤ q e)
    (a : Fin (SparseOuterLaw.law D c q hc hq).length) :
    opening D c q Δ (SparseOuterLaw.law D c q hc hq).states[a.val] ≤
      (n:ℚ)*(Δ:ℚ)+(∑ e,SparseSignedPreparation.signed D c e*q e)+3+
       ∑ j,discarded D q Δ (SparseOuterLaw.law D c q hc hq).states[a.val] j := by
  rw [raw_identity]
  have hh := (SparseOuterLaw.budget D c q hc hq a).2.2.2.2.2
  linarith only [hh]

end MetricKMedian.SparsePrepared
end
end

end OAI
end


