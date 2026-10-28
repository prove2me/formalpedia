-- Prove2me | Definitions.Def_OAIQ035K064
-- name    : OAIQ035K064
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:18:30.625997+00:00
-- url     : https://prove2.me/theorems/59a4fe80-4184-4c32-861c-6a2098351255
-- title:
--   Definitions bundle OAIQ035K064 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 20 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Sparse_SparseCardinalRounding`, `KMedian_Sparse_SparseCountFeatures`, `KMedian_Sparse_SparseCountRun`, `KMedian_Sparse_SparseGraphFeatures`, `KMedian_Sparse_SparseGraphRun`, `KMedian_Sparse_SparseSignedFixed`, `KMedian_Sparse_SparseSignedPartial`, `KMedian_Sparse_SparseWeightedPartial`.
--
--   **Imports.** It imports the bundles `OAIQ035K044`, `OAIQ035K055`, `OAIQ035K056` and `OAIQ035K057` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ035K068`; the proofs of `OAI.MetricKMedian.RationalPhysicalKernel.graph_data_all` and `OAI.MetricKMedian.Taper.physical_sparse_graph`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K044
import Definitions.Def_OAIQ035K055
import Definitions.Def_OAIQ035K056
import Definitions.Def_OAIQ035K057

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseWeightedPartial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseWeightedPartial
open Finset RationalWeightedStep
variable {n : ℕ}

 theorem step_pair (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (μ : SparseIntegerLaw (Vector ℚ n)) (i j : Fin n) (hij : i ≠ j) :
    (step β hβ μ).moment (fun p => point p i*point p j) ≤
      μ.moment (fun p => point p i*point p j) := by
  have hh := μ.step_moment features (probability β) (probability_unit β hβ)
    (endpoint β) (finSumFinEquiv (Sum.inr (finProdFinEquiv (i,j))))
  simp only [features_pair] at hh
  exact hh.trans_le (μ.moment_mono _ _ (fun k => endpoint_pair β hβ _ i j hij))

 theorem run_pair (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (t : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (run β hβ p t).moment (fun q => point q i*point q j) ≤ point p i*point p j := by
  induction t with
  | zero => exact (SparseIntegerLaw.dirac_moment _ _).le
  | succ t ih => exact (step_pair β hβ _ i j hij).trans ih

end MetricKMedian.SparseWeightedPartial
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseCardinalRounding
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

theorem round_pair (p : Vector ℚ n) (i j : Fin n) (hij : i ≠ j) :
    (round p).moment (fun q => point q i*point q j) ≤ point p i*point p j :=
  SparseWeightedPartial.run_pair _ _ p n i j hij

end MetricKMedian.SparseCardinalRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseCountFeatures
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseCountRun
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

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseGraphFeatures
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseGraphRun
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSignedPartial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSignedPartial
open Finset RationalSignedStep
open RationalWeightedStep (point fractional)
open SparseWeightedPartial (features features_single features_pair)
variable {n : ℕ}

 theorem step_mean (β : Fin n → ℚ) 
    (μ : SparseIntegerLaw (Vector ℚ n)) (i : Fin n) :
    (step β μ).moment (fun p => point p i)=μ.moment (fun p => point p i) := by
  have hh := μ.step_moment features (probability β) (probability_unit β)
    (endpoint β) (finSumFinEquiv (Sum.inl i))
  simp only [features_single] at hh
  exact hh.trans (μ.moment_congr _ _ (fun a => endpoint_mean β _ i))

 theorem step_pair (β : Fin n → ℚ) 
    (μ : SparseIntegerLaw (Vector ℚ n)) (i j : Fin n) (hij : i ≠ j) :
    (step β μ).moment (fun p => point p i*point p j) ≤
      μ.moment (fun p => point p i*point p j) := by
  have hh := μ.step_moment features (probability β) (probability_unit β)
    (endpoint β) (finSumFinEquiv (Sum.inr (finProdFinEquiv (i,j))))
  simp only [features_pair] at hh
  exact hh.trans_le (μ.moment_mono _ _ (fun k => endpoint_pair β _ i j hij))

 theorem run_mean (β : Fin n → ℚ) 
    (p : Vector ℚ n) (t : ℕ) (i : Fin n) :
    (run β p t).moment (fun q => point q i)=point p i := by
  induction t with
  | zero => exact SparseIntegerLaw.dirac_moment _ _
  | succ t ih => rw [run,step_mean,ih]

 theorem run_pair (β : Fin n → ℚ) 
    (p : Vector ℚ n) (t : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (run β p t).moment (fun q => point q i*point q j) ≤ point p i*point p j := by
  induction t with
  | zero => exact (SparseIntegerLaw.dirac_moment _ _).le
  | succ t ih => exact (step_pair β _ i j hij).trans ih

end MetricKMedian.SparseSignedPartial
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSignedFixed
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

theorem positive (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1)
    (a : Fin (round u p hp).length) : 0 < (round u p hp).law.rational.weight a := by
  exact ((SparseSignedPartial.run u p n).bindIndexed (kernel u p hp)).compressAuto_positive features a

end MetricKMedian.SparseSignedRounding
end
end

end OAI
end


