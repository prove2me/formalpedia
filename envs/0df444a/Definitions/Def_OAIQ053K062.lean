-- Prove2me | Definitions.Def_OAIQ053K062
-- name    : OAIQ053K062
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:14:33.244992+00:00
-- url     : https://prove2.me/theorems/5dc3c4d6-75a6-4d5a-bcc7-38ceea0da4b4
-- title:
--   Definitions bundle OAIQ053K062 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`KMedian_Sparse_SparseCountFeatures`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseCountFeatures.lean), [`KMedian_Sparse_SparseCountRun`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Sparse/SparseCountRun.lean).
--
--   **Imports.** It imports the bundles `OAIQ053K036` and `OAIQ053K051` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ053K069`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K036
import Definitions.Def_OAIQ053K051

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

theorem step_pair (μ : SparseIntegerLaw (Table n m)) (ν : SparseIntegerLaw ((Fin n → ℕ)))
    (i j k : Fin m) (h l : Fin n) (hjk : j≠k) :
    (step μ ν i).moment (fun G => edge G h j*edge G l k)=
      if j=i then ν.moment (fun S => (S h:ℚ))*μ.moment (fun G => edge G l k)
      else if k=i then μ.moment (fun G => edge G h j)*ν.moment (fun S => (S l:ℚ))
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

theorem step_same (μ : SparseIntegerLaw (Table n m)) (ν : SparseIntegerLaw (Fin n → ℕ))
    (i j : Fin m) (h l : Fin n) :
    (step μ ν i).moment (fun G => edge G h j*edge G l j)=
      if j=i then ν.moment (fun S => (S h:ℚ)*(S l:ℚ))
      else μ.moment (fun G => edge G h j*edge G l j) := by
  have hh := (μ.prodCompress_spec ν (fun G S => next G S i) features).2.2
    (finSumFinEquiv (Sum.inr (finProdFinEquiv (finProdFinEquiv (h,j),finProdFinEquiv (l,j)))))
  simp only [features_pair] at hh
  refine hh.trans ?_
  by_cases hji : j=i
  · simp only [edge_next,ite_eq_left hji]
    exact μ.moment_const _
  · simp only [edge_next,ite_eq_right hji,SparseIntegerLaw.moment_const]

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

theorem run_same (ν : Fin m → SparseIntegerLaw (Fin n → ℕ))
    (t : ℕ) (ht : t ≤ m) (h l : Fin n) (i : Fin m) :
    (run ν t).moment (fun G => edge G h i*edge G l i)=
      if i.val<t then (ν i).moment (fun S => (S h:ℚ)*(S l:ℚ)) else 0 := by
  induction t with
  | zero => simp [run,SparseIntegerLaw.dirac_moment,edge]
  | succ t ih =>
    have htm : t < m := by omega
    rw [run,dite_eq_left htm,step_same]
    by_cases hi : i=⟨t,htm⟩
    · subst i
      simp only [Nat.lt_succ_self,ite_true]
    · rw [ite_eq_right hi,ih (by omega)]
      have hv : i.val≠t := fun he => hi (Fin.ext he)
      have hh : i.val<t+1 ↔ i.val<t := by omega
      simp only [hh]

end MetricKMedian.SparseCounts
end
end

end OAI
end


