-- Prove2me | Definitions.Def_OAIQ035K032
-- name    : OAIQ035K032
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T08:00:06.981016+00:00
-- url     : https://prove2.me/theorems/362ec798-929b-4a04-bf9f-ce9cbc2121c3
-- title:
--   Definitions bundle OAIQ035K032 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 43 declarations of OpenAI's Lean: 22 definitions and 21 theorems. The definitions and types are `OAI.MetricKMedian.Instance.clientDistance`, `OAI.MetricKMedian.Instance.computedFractional`, `OAI.MetricKMedian.Instance.zeroTest`, `OAI.MetricKMedian.LPBinary.Input.raw`, `OAI.MetricKMedian.LPBinary.Nearest.ee`, `OAI.MetricKMedian.LPBinary.Nearest.ees`, `OAI.MetricKMedian.LPBinary.Nearest.filling`, `OAI.MetricKMedian.Preparation.FractionalRefinement.Program.assignmentData`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyNext.instLinearOrderSubtypeCopyFinMemFinset`, `OAI.MetricKMedian.SparseBernoulli.ListOperation.er`, `OAI.MetricKMedian.SparseBernoulli.Program.Context.raw`, `OAI.MetricKMedian.SparseBernoulli.Program.T`, `OAI.MetricKMedian.SparseBernoulli.Program.endpoint`, `OAI.MetricKMedian.SparseBernoulli.Program.er`, `OAI.MetricKMedian.SparseBernoulli.Program.probability`, `OAI.MetricKMedian.SparseBernoulli.Program.view`, `OAI.MetricKMedian.SparseCardinalRounding.Program.qr`, `OAI.MetricKMedian.TruncatedLP.approximation`, `OAI.MetricKMedian.TruncatedLP.feasibleScales`, `OAI.MetricKMedian.TruncatedLP.scaledCandidate`, `OAI.MetricKMedian.TruncatedLP.selectFractional`, `OAI.MetricKMedian.rationalCost`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Geometry_GraphRunHeight`, `KMedian_Geometry_RationalInstanceCost`, `KMedian_Optimization_ApproximateFractional`, `KMedian_Optimization_ApproximateLPSelection`, `KMedian_Optimization_ComputedNearest`, `KMedian_Optimization_FractionalInputProgram`, `KMedian_Optimization_IndexedInstanceLP`, `KMedian_Optimization_LPBinaryInput`, `KMedian_Optimization_TruncatedOptimization`, `KMedian_Optimization_ZeroCostBranch`, `KMedian_Preparation_RationalSupplierScan`, `KMedian_Probability_BernoulliListOperations`, `KMedian_Probability_BernoulliRunHeight`, `KMedian_Probability_BernoulliStepProgram`, `KMedian_Process_BatchOrdinalCodes`, `KMedian_Process_CopyNextProgram`, `KMedian_Process_RoundingStateCompiler`, `KMedian_Programs_CardinalRoundProgram`, `KMedian_Programs_InstanceFractionalRound`, `KMedian_Programs_NearestListProgram`, `KMedian_Programs_PivotListProgram`, `KMedian_Programs_RationalSortProgram`, `KMedian_Reduction_NormalizationGuesses`, `KMedian_Sparse_SparseBindProgram`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K014`, `OAIQ035K015`, `OAIQ035K016`, `OAIQ035K017`, `OAIQ035K018`, `OAIQ035K019`, `OAIQ035K020`, `OAIQ035K021` and `OAIQ035K022` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K041`, `OAIQ035K042`, `OAIQ035K043`, `OAIQ035K044` and `OAIQ035K062`; the proofs of `OAI.MetricKMedian.Reduction.CloseCenters.completionSet_spec` and `OAI.MetricKMedian.Reduction.completion_branch_exists`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K014
import Definitions.Def_OAIQ035K015
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K017
import Definitions.Def_OAIQ035K018
import Definitions.Def_OAIQ035K019
import Definitions.Def_OAIQ035K020
import Definitions.Def_OAIQ035K021
import Definitions.Def_OAIQ035K022

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_GraphRunHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.SparseGraph
open Binary
variable {n m : ℕ}

theorem edge_height (G : Graph n m) (h : Fin n) (i : Fin m) : HasHeight (edge G h i) 0 := by
  unfold edge
  split_ifs
  · exact HasHeight.one 0
  · exact HasHeight.zero 0

theorem features_height (G : Graph n m) (a : Fin (n*m+(n*m)*(n*m))) : HasHeight (features G a) 0 := by
  unfold features edgeCode
  generalize finSumFinEquiv.symm a=z
  cases z with
  | inl i => exact edge_height _ _ _
  | inr ij => exact (edge_height _ _ _).mul (edge_height _ _ _)

end MetricKMedian.SparseGraph
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalInstanceCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset

def rationalCost (I : Instance) (S : Finset (Fin I.n)) : ℚ :=
  ∑ j ∈ I.clients, rationalNearest I j S

namespace Instance

theorem cast_rationalNearest (I : Instance) (j : Fin I.n) (S : Finset (Fin I.n)) :
    (rationalNearest I j S:ℝ)=nearest I j S := by
  by_cases hS : S.Nonempty
  · rw [rationalNearest,dite_eq_left hS,nearest,dite_eq_left hS]
    apply le_antisymm
    · apply le_min'
      intro q hq
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hq
      exact_mod_cast min'_le _ _ (mem_image_of_mem (I.distance j) hi)
    · obtain ⟨i,hi,he⟩ := mem_image.mp (min'_mem (S.image (I.distance j)) (hS.image _))
      rw [← he]
      exact min'_le _ _ (mem_image_of_mem (fun i => (I.distance j i:ℝ)) hi)
  · simp only [rationalNearest,dite_eq_right hS,nearest,Rat.cast_zero]

theorem cast_rationalCost (I : Instance) (S : Finset (Fin I.n)) :
    (rationalCost I S:ℝ)=cost I S := by
  simp only [rationalCost,Rat.cast_sum,I.cast_rationalNearest,cost]

end Instance
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_ComputedNearest
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
-- module Solutions.OAIQ035_KM.KMedian_Optimization_TruncatedOptimization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset ProjectedSubgradient
variable {n m : ℕ} [NeZero n] [NeZero m]

theorem optimize_spec (d : Fin m → Fin n → ℚ) (r k H : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hH : 0 < H) (hd : ∀ j i, 0 ≤ d j i)
    (z : Fin n → ℚ) (hz : feasible (k:ℚ) z) :
    feasible (k:ℚ) (point (optimize d r k H hr hk hH)) ∧
      objective d (point (optimize d r k H hr hk hH)) H ≤ objective d z H+1/(r:ℚ) := by
  let T := steps (n:=n) (m:=m) r k H
  let : NeZero T := ⟨(steps_pos r k H hr hk hH).ne'⟩
  let v := trajectory (k:ℚ) (rate (n:=n) (m:=m) r H)
    (fun y => gradient d y H) (initial (k:ℚ))
  let a := Preparation.firstNearest (univ:Finset (Fin T))
    (fun t => objective d (point (v t.val)) H) univ_nonempty
  have hkq : (0:ℚ) < k := by exact_mod_cast hk
  have hHq : (1:ℚ) ≤ H := by exact_mod_cast hH
  have hstart := initial_feasible (n:=n) (k:ℚ) hkq.le
  have hh := Preparation.firstNearest_spec (univ:Finset (Fin T))
    (fun t => objective d (point (v t.val)) H) univ_nonempty
  change feasible (k:ℚ) (point (v a.val)) ∧
    objective d (point (v a.val)) H ≤ objective d z H+1/(r:ℚ)
  refine ⟨trajectory_feasible _ _ _ _ hkq hstart _,?_⟩
  obtain ⟨t,ht,htc⟩ := exists_accurate (fun y => objective d y H) (fun y => gradient d y H)
    (k:ℚ) (rate (n:=n) (m:=m) r H) (gradSize (n:=n) (m:=m) H:ℚ) (1/(r:ℚ))
    hkq (rate_pos r H hr hH) (initial (k:ℚ)) hstart z hz
    (fun y _ => subgradient d y z H)
    (fun y _ => by
      simpa only [gradSize,Fintype.card_fin,Nat.cast_mul,Nat.cast_pow] using
        gradient_sq_bound d y H hHq hd)
    T (steps_pos r k H hr hk hH) (iteration_bound r k H hr hH _ z hstart hz)
  exact (hh.2 ⟨t,mem_range.mp ht⟩ (mem_univ _)).trans htc

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_ApproximateFractional
attribute [-instance] _root_.OAI.MetricKMedian.TruncatedLP.instDecidableValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset ProjectedSubgradient
variable {n m : ℕ} [NeZero n] [NeZero m]

def approximation (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i) : FractionalData n m :=
  let H := penalty r k
  let y := point (optimize d r k H hr hk (penalty_pos r k hr))
  have hy : feasible (k:ℚ) y := (optimize_spec d r k H hr hk (penalty_pos r k hr) hd
    (point (initial (k:ℚ))) (initial_feasible _ (by positivity))).1
  have hym : 1 ≤ ∑ i, y i := by rw [hy.2]; exact_mod_cast hk
  let x := fun j => point (Preparation.computedNearest y (truncated d H j) hy.1 hym)
  ⟨Vector.ofFn (repairedOpening y (loss r k)),
    Vector.ofFn (fun j => Vector.ofFn (repairedAssignment d x j))⟩

theorem approximation_spec (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i)
    (s : ℚ) (hs : 1/2 ≤ s) (hs1 : s ≤ 1)
    (z : Fin n → ℚ) (hz : feasible (k:ℚ) z)
    (hzc : objective d z (penalty r k) ≤ s) :
    let a := approximation d r k hr hk hd
    (∀ i : Fin n, 0 ≤ a.opening[i.val] ∧ a.opening[i.val] ≤ 1) ∧
    (∀ (j : Fin m) (i : Fin n), 0 ≤ a.assignment[j.val][i.val] ∧
      a.assignment[j.val][i.val] ≤ a.opening[i.val]) ∧
    (∀ j : Fin m, ∑ i : Fin n, a.assignment[j.val][i.val]=1) ∧
    (∑ i : Fin n, a.opening[i.val]) ≤ (k:ℚ)+1 ∧
    (∑ j : Fin m, ∑ i : Fin n, a.assignment[j.val][i.val]*d j i) ≤ (1+3/(r:ℚ))*s := by
  let H := penalty r k
  let y := point (optimize d r k H hr hk (penalty_pos r k hr))
  have hyc := optimize_spec d r k H hr hk (penalty_pos r k hr) hd z hz
  have hy : feasible (k:ℚ) y := hyc.1
  have hym : 1 ≤ ∑ i, y i := by rw [hy.2]; exact_mod_cast hk
  let x := fun j => point (Preparation.computedNearest y (truncated d H j) hy.1 hym)
  have hx := fun j => Preparation.computedNearest_spec y (truncated d H j) hy.1 hym H
  have hxe : (∑ j, ∑ i, x j i*truncated d H j i)=objective d y H := by
    exact sum_congr rfl (fun j _ => (hx j).2.2)
  have hc : (∑ j, ∑ i, x j i*truncated d H j i) ≤ s+1/(r:ℚ) := by
    rw [hxe]
    exact hyc.2.trans (by dsimp [H] at *; linarith)
  have hcost : (∑ j, ∑ i, x j i*truncated d H j i) ≤ loss r k*(H:ℚ) := by
    have he : loss r k*(H:ℚ)=1+1/(r:ℚ) := by
      unfold loss
      exact div_mul_cancel₀ _ (by exact_mod_cast (penalty_pos r k hr).ne')
    rw [he]
    exact hc.trans (by linarith)
  obtain ⟨_,_,hρ,hkρ⟩ := loss_bounds r k hr hk
  obtain ⟨h1,h2,h3,h4,h5⟩ := repaired_spec d x y H (loss r k) k
    (penalty_one r k hr) hρ hkρ hd hy.1 (fun j => (hx j).1)
    (fun j => (hx j).2.1) hy.2.le hcost
  have hfinal := h5.trans ((div_le_div_of_nonneg_right hc (sub_pos.mpr hρ).le).trans
    (repair_error r k hr hk s hs))
  simpa only [approximation,Vector.getElem_ofFn] using And.intro h1 (And.intro h2
    (And.intro h3 (And.intro h4 hfinal)))

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_NormalizationGuesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset

namespace Instance

theorem rationalNearest_attained (I : Instance) (j : Fin I.n)
    (S : Finset (Fin I.n)) (hS : S.Nonempty) :
    ∃ i ∈ S, rationalNearest I j S=I.distance j i := by
  unfold rationalNearest
  rw [dite_eq_left hS]
  obtain ⟨i,hi,he⟩ := mem_image.mp (min'_mem (S.image (I.distance j)) (hS.image _))
  exact ⟨i,hi,he.symm⟩

end Instance

end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_ApproximateLPSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset
variable {n m : ℕ} [NeZero n] [NeZero m]

def scaledCandidate (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i) (B : ℚ) : FractionalData n m :=
  if hB : 0 < B then
    approximation (fun j i => d j i/B) r k hr hk (fun j i => div_nonneg (hd j i) hB.le)
  else ⟨Vector.replicate n 0,Vector.replicate m (Vector.replicate n 0)⟩

def feasibleScales (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i) : Finset ℚ :=
  (Normalization.matrixGuesses d).filter
    (fun B => (scaledCandidate d r k hr hk hd B).Valid k)

def selectFractional (d : Fin m → Fin n → ℚ) (r k : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hd : ∀ j i, 0 ≤ d j i) : FractionalData n m :=
  scaledCandidate d r k hr hk hd
    (rationalArgmin (feasibleScales d r k hr hk hd)
      (fun B => (scaledCandidate d r k hr hk hd B).value d))

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPBinaryInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.LPBinary
open Binary Polynomial Finset

namespace Input
def raw (I : Input) : Rows × ℕ := (I.rows,I.k)
end Input

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_NearestListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset

namespace Nearest
abbrev ee := encodePair Nat.bits (encodePair Ratio.encode Ratio.encode)
abbrev ees := encodeList ee

def filling (ys ds : Row) : Row := let es := entries ys ds; es.map (amount es)

end Nearest
end MetricKMedian.LPBinary
end

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
open Binary Binary.PolyProgram Function Finset

theorem least_ofFn {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ)
    (h : (positiveSet z).Nonempty) :
    least (List.ofFn (fun i => (μ.numerator i,z i)))=leastRatio μ z h := by
  apply LPBinary.minimum_eq_finset
  intro q
  simp only [List.mem_map,List.mem_filter,List.mem_ofFn,decide_eq_true_eq,mem_image,positiveSet,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨e,⟨⟨i,rfl⟩,hi⟩,rfl⟩
    exact ⟨i,hi,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨(μ.numerator i,z i),⟨⟨i,rfl⟩,hi⟩,rfl⟩

theorem pivot_ofFn {n : ℕ} (μ : IntegerLaw (Fin n)) (z : Fin n → ℤ)
    (h : (positiveSet z).Nonempty) :
    pivot (List.ofFn (fun i => (μ.numerator i,z i)))=(computedPivot μ z h).val := by
  unfold pivot
  rw [least_ofFn μ z h]
  let p := computedPivot μ z h
  apply (List.findIdx_eq (by simpa only [List.length_ofFn] using p.isLt)).mpr
  constructor
  · have hp := mem_filter.mp (min'_mem (pivotSet μ z h) (pivotSet_nonempty μ z h))
    simpa only [List.getElem_ofFn,decide_eq_true_eq,ratio,IntegerLaw.ratio] using ⟨(mem_filter.mp hp.1).2,hp.2⟩
  · intro j hj
    simp only [List.getElem_ofFn,decide_eq_false_iff_not]
    intro hp
    have hm : p ≤ (⟨j,Nat.lt_trans hj p.isLt⟩ : Fin n) := min'_le (pivotSet μ z h) _
      (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hp.1⟩,hp.2⟩)
    exact (not_le_of_gt hj) hm

end MetricKMedian.IntegerLaw.ListPivot
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_RationalSupplierScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars

namespace FixedParameters
theorem positive {τ : ℝ} (qR : FixedBatch.RationalParameters τ) : 0<qR.g := by exact_mod_cast qR.gpos
end FixedParameters

end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_RationalSortProgram
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

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_FractionalInputProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.FractionalRefinement.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MetricKMedian.MaskProgram

def assignmentData (z : Raw) : Matrix := z.2.1.map (fun d => LPBinary.Nearest.filling z.1 d)
end MetricKMedian.Preparation.FractionalRefinement.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_IndexedInstanceLP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset
namespace Instance

theorem indexed_integral (I : Instance) (S : Finset (Fin I.n))
    (hSF : S ⊆ I.facilities) (hS : S.Nonempty) :
    ∃ T : Finset (Fin I.facilities.card), T.Nonempty ∧ T.card=S.card ∧
      ∃ a : Fin I.clients.card → Fin I.facilities.card, (∀ j, a j ∈ T) ∧
        (∑ j, I.indexedDistance j (a j))=rationalCost I S := by
  classical
  let f := I.facilities.orderEmbOfFin rfl
  let T := S.preimage f f.injective.injOn
  have hT : T.card=S.card := by
    rw [card_preimage]
    change ({x ∈ S | x ∈ Set.range (I.facilities.orderEmbOfFin rfl)}).card=S.card
    simp only [range_orderEmbOfFin]
    congr 1
    exact filter_eq_self.mpr hSF
  have hTn : T.Nonempty := card_pos.mp (by rw [hT]; exact card_pos.mpr hS)
  have each : ∀ j : Fin I.clients.card, ∃ i : Fin I.facilities.card,
      i ∈ T ∧ I.indexedDistance j i=rationalNearest I (I.clients.orderEmbOfFin rfl j) S := by
    intro j
    obtain ⟨i,hi,hd⟩ := I.rationalNearest_attained (I.clients.orderEmbOfFin rfl j) S hS
    let b : ↥I.facilities := ⟨i,hSF hi⟩
    let ai := (I.facilities.orderIsoOfFin rfl).symm b
    have he : f ai=i := congrArg Subtype.val ((I.facilities.orderIsoOfFin rfl).apply_symm_apply b)
    refine ⟨ai,mem_preimage.mpr ?_,?_⟩
    · rwa [he]
    · change I.distance _ (f ai)=_
      rw [he,hd]
  choose a ha hd using each
  refine ⟨T,hTn,hT,a,ha,?_⟩
  calc
    _ = ∑ j : Fin I.clients.card, rationalNearest I (I.clients.orderEmbOfFin rfl j) S :=
      sum_congr rfl (fun j _ => hd j)
    _ = ∑ j : ↥I.clients, rationalNearest I j.val S :=
      (I.clients.orderIsoOfFin rfl).toEquiv.sum_comp (fun j => rationalNearest I j.val S)
    _ = _ := sum_coe_sort I.clients (fun j => rationalNearest I j S)

def computedFractional (I : Instance) (r : ℕ) (hr : 0 < r)
    (hJ : I.clients.Nonempty) : TruncatedLP.FractionalData I.facilities.card I.clients.card :=
  letI : NeZero I.facilities.card := ⟨(card_pos.mpr I.facilities_nonempty).ne'⟩
  letI : NeZero I.clients.card := ⟨(card_pos.mpr hJ).ne'⟩
  TruncatedLP.selectFractional I.indexedDistance r I.k hr I.k_pos I.indexedDistance_nonneg

end Instance
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_ZeroCostBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset
namespace Instance

def zeroTest (I : Instance) : Prop := I.clients ⊆ I.facilities ∧ I.clients.card ≤ I.k

end Instance
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.SparseBernoulli.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly
abbrev er := encodeList encodeBool

end MetricKMedian.SparseBernoulli.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliRunHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.SparseBernoulli
open Binary
variable {n d : ℕ}

theorem features_height (q : Fin n → Bool) (a : Fin ((n+1)^d)) : HasHeight (features q a) 0 := by
  unfold features monomial
  rw [ListOperation.flag_product]
  split_ifs
  · exact HasHeight.one 0
  · exact HasHeight.zero 0

end MetricKMedian.SparseBernoulli
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundingStateCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse

theorem trimData_map {α β : Type} (f : α → β) (d : Data α) :
    trimData (d.1,d.2.map f)=((trimData d).1,(trimData d).2.map f) := by
  have hz : d.1.2.zip (d.2.map f)=(d.1.2.zip d.2).map (fun z => (z.1,f z.2)) := by
    exact List.zip_map_right
  simp only [trimData,activeEntries,hz,List.filter_map,List.map_map,Function.comp_def]

end MetricKMedian.RoundingProgram
end

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
abbrev er := ListOperation.er
abbrev Context.raw (c : Context) := (List.ofFn c.input.p,c.t)
abbrev T (c : Context) := Fin c.input.n → Bool
abbrev view (c : Context) (q : T c) := List.ofFn q

def probability (c : Context) (_ : T c) : ℚ := if h : c.t < c.input.n then c.input.p ⟨c.t,h⟩ else 0
def endpoint (c : Context) (q : T c) (b : Fin 2) : T c :=
  fun i => if i.val=c.t then decide (b=0) else q i
 theorem probability_unit (c : Context) (q : T c) : 0 ≤ probability c q ∧ probability c q ≤ 1 := by
  unfold probability
  split_ifs with h
  · exact c.input.feasible _
  · norm_num

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_BatchOrdinalCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.RationalBatchData.Ordinal
open Finset FixedBatch
open SparseGraph.ListOperation (Row Table setView indices)
variable {I : Type} [LinearOrder I] {n : ℕ}
variable (r : Fin n ≃o I) (D : Actions I I) (H : Finset I)

 theorem enumeration_strictMono [Fintype I] : StrictMono (fun i => code r D H (enumeration D H i)) := by
  let : LinearOrder (I × I) := pairOrder (I:=I)
  let : LinearOrder (HeavyAction D H) := actionOrder D H
  intro i j hij
  apply code_strictMono r D H
  exact @OrderIso.strictMono _ _ _ (actionOrder D H).toPreorder
    (@Fintype.orderIsoFinOfCardEq (HeavyAction D H) (actionOrder D H) _ _ rfl) i j hij
end MetricKMedian.RationalBatchData.Ordinal
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
abbrev qr := encodeList Ratio.encode
end MetricKMedian.SparseCardinalRounding.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyNextProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.RationalPhysicalKernel.CopyNext
open Binary Binary.Automatic Binary.Automatic.Poly Finset FixedBatch
open CopyList
open CopyGraphProgram (rank_owner)
open SparseGraph.ListOperation (Row Table setView indices)
local instance instLinearOrderSubtypeCopyFinMemFinset {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : LinearOrder ↥A := activeOrder A

end MetricKMedian.RationalPhysicalKernel.CopyNext
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_InstanceFractionalRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.Instance
open Finset Preparation

 def clientDistance (I : Instance) (c c' : Fin I.clients.card) : ℚ :=
  I.distance (I.clients.orderEmbOfFin rfl c) (I.clients.orderEmbOfFin rfl c')

 theorem clientDistance_self (I : Instance) (c : Fin I.clients.card) : I.clientDistance c c=0 :=
  (I.distance_eq_zero _ _).mpr rfl

 theorem clientDistance_comm (I : Instance) (c c' : Fin I.clients.card) :
    I.clientDistance c c'=I.clientDistance c' c := I.distance_symm _ _

end MetricKMedian.Instance
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBindProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.Automatic Binary.Automatic.Poly Finset

variable {α β A : Type}

 theorem weights_law {n : ℕ} (μ : IntegerLaw (Fin n)) :
    weights (μ.denominator,List.ofFn μ.numerator)=List.ofFn μ.rational.weight := by
  simp only [weights,List.map_ofFn,Function.comp_def,IntegerLaw.rational]

 theorem scaling_numerator_equiv {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (w : ι → ℚ) (j : κ) :
    RationalScaling.numerator (fun j => w (e.symm j)) j=RationalScaling.numerator w (e.symm j) := by
  apply Int.cast_injective (α:=ℚ)
  rw [RationalScaling.numerator_cast,RationalScaling.numerator_cast,scaling_denominator_equiv]

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end


