-- Prove2me | Definitions.Def_OAIQ035K008
-- name    : OAIQ035K008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:54:15.354366+00:00
-- url     : https://prove2.me/theorems/6a21bec7-c182-44e3-a622-7c21abe11cb9
-- title:
--   Definitions bundle OAIQ035K008 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 77 declarations of OpenAI's Lean: 47 definitions, 2 inductive types or structures, 1 instance and 27 theorems. The definitions and types are `OAI.MetricKMedian.FractionalDual.thresholds`, `OAI.MetricKMedian.GeneratorAverage.external`, `OAI.MetricKMedian.GeneratorAverage.inside`, `OAI.MetricKMedian.GraphComparison.externalMass`, `OAI.MetricKMedian.GraphComparison.externalSquare`, `OAI.MetricKMedian.GraphComparison.kernel`, `OAI.MetricKMedian.GraphComparison.rowType`, `OAI.MetricKMedian.GraphLaw.edge`, `OAI.MetricKMedian.GraphMoments.kernel`, `OAI.MetricKMedian.GraphMoments.removedCost`, `OAI.MetricKMedian.GraphMoments.removedMass`, `OAI.MetricKMedian.GroupCap.cap`, `OAI.MetricKMedian.InputParser.State`, `OAI.MetricKMedian.InputParser.parseStep`, `OAI.MetricKMedian.InputParser.width`, `OAI.MetricKMedian.Instance.indexedDistance`, `OAI.MetricKMedian.Instance.pseudoMetric`, `OAI.MetricKMedian.LPBinary.Nearest.Entry`, `OAI.MetricKMedian.LPBinary.Nearest.amount`, `OAI.MetricKMedian.LPBinary.Nearest.before`, `OAI.MetricKMedian.LPBinary.Nearest.prior`, `OAI.MetricKMedian.Normalization.matrixGuesses`, `OAI.MetricKMedian.Preparation.Filling`, `OAI.MetricKMedian.Preparation.FractionalRefinement.Program.Matrix`, `OAI.MetricKMedian.Preparation.FractionalRefinement.Program.Raw`, `OAI.MetricKMedian.Preparation.FractionalRefinement.y`, `OAI.MetricKMedian.Preparation.RationalSplitting.Program.Raw`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.BTable`, `OAI.MetricKMedian.Preparation.RationalUnitInput.Program.pickRows`, `OAI.MetricKMedian.ProjectedSubgradient.feasible`, `OAI.MetricKMedian.ProjectedSubgradient.initial`, `OAI.MetricKMedian.ProjectedSubgradient.next`, `OAI.MetricKMedian.ProjectedSubgradient.point`, `OAI.MetricKMedian.ProjectedSubgradient.sqdist`, `OAI.MetricKMedian.ProjectedSubgradient.trajectory`, `OAI.MetricKMedian.RationalSortProgram.insertData`, `OAI.MetricKMedian.Simplex.level`, `OAI.MetricKMedian.Simplex.project`, `OAI.MetricKMedian.Simplex.threshold`, `OAI.MetricKMedian.Simplex.upper` and 9 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Binary_InstanceParserProgram`, `KMedian_Binary_NumericParserProgram`, `KMedian_Binary_SequentialParserProgram`, `KMedian_Geometry_GraphComparison`, `KMedian_Geometry_GraphLaw`, `KMedian_Geometry_GraphMoments`, `KMedian_Geometry_RationalFractionalInput`, `KMedian_Instance`, `KMedian_Optimization_ApproximateFractional`, `KMedian_Optimization_ApproximateLPSelection`, `KMedian_Optimization_ComputedNearest`, `KMedian_Optimization_FractionalDual`, `KMedian_Optimization_FractionalInputProgram`, `KMedian_Optimization_IndexedInstanceLP`, `KMedian_Optimization_MatrixNormalization`, `KMedian_Optimization_ProjectedSubgradient`, `KMedian_Optimization_SimplexDiameter`, `KMedian_Optimization_SimplexProjection`, `KMedian_Optimization_TruncatedObjective`, `KMedian_Optimization_TruncatedOptimization`, `KMedian_Preparation_SupplierListOperations`, `KMedian_Process_GeneratorAverage`, `KMedian_Process_GroupCap`, `KMedian_Programs_NearestListProgram`, `KMedian_Programs_RationalSortProgram`, `KMedian_Programs_SplitListProgram`, `KMedian_Programs_UnitGeometryProgram`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K020`, `OAIQ035K021`, `OAIQ035K022`, `OAIQ035K023`, `OAIQ035K024`, `OAIQ035K025`, `OAIQ035K026`, `OAIQ035K044` and `OAIQ035K062`; the statement `OAI.MetricKMedian.GeneratorAverage.averaged_ideal_drift`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_NumericParserProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.InputParser
def width (xs : List Bool) : ℕ := xs.findIdx Bool.not
end MetricKMedian.InputParser
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_SequentialParserProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.InputParser
open Polynomial
section Generic
variable {α : Type}
  [Inhabited α]
  (read : List Bool → α × List Bool)
abbrev State := List Bool × List α
def parseStep (x : State (α:=α) × Unit) : State (α:=α) :=
  let s := read x.1.1
  (s.2,s.1::x.1.2)
end Generic
end MetricKMedian.InputParser
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_FractionalDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FractionalDual
open Finset
variable {ι : Type} [Fintype ι]

def thresholds (d : ι → ℚ) (H : ℚ) : Finset ℚ := insert 0 (insert H (univ.image d))

end MetricKMedian.FractionalDual
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

structure Filling (U : Finset (Fin n)) (y d : Fin n → ℚ) (t : ℚ) where
  amount : Fin n → ℚ
  outside : ∀ i, i ∉ U → amount i=0
  bounds : ∀ i ∈ U, 0 ≤ amount i ∧ amount i ≤ y i
  total : ∑ i ∈ U, amount i=t
  ordered : ∀ i ∈ U, ∀ a ∈ U, 0 < amount i → amount a < y a → d i ≤ d a

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_SimplexProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Simplex
open Finset
variable {ι : Type} [Fintype ι] [Nonempty ι]

def upper (x : ι → ℚ) (a : ι) : Finset ι := univ.filter (fun i => x a ≤ x i)

omit [Nonempty ι] in
theorem mem_upper_self (x : ι → ℚ) (a : ι) : a ∈ upper x a := by simp [upper]

omit [Nonempty ι] in
theorem upper_card_pos (x : ι → ℚ) (a : ι) : 0 < (upper x a).card :=
  card_pos.mpr ⟨a,mem_upper_self x a⟩

def threshold (x : ι → ℚ) (k : ℚ) (a : ι) : ℚ :=
  ((∑ i ∈ upper x a, x i)-k)/(upper x a).card

def level (x : ι → ℚ) (k : ℚ) : ℚ :=
  (univ.image (threshold x k)).max' (univ_nonempty.image _)

def project (x : ι → ℚ) (k : ℚ) (i : ι) : ℚ := max 0 (x i-level x k)

theorem threshold_le_level (x : ι → ℚ) (k : ℚ) (a : ι) :
    threshold x k a ≤ level x k :=
  le_max' _ _ (mem_image.mpr ⟨a,mem_univ _,rfl⟩)

theorem level_attained (x : ι → ℚ) (k : ℚ) : ∃ a, level x k=threshold x k a := by
  obtain ⟨a,_,ha⟩ := mem_image.mp (max'_mem (univ.image (threshold x k))
    (univ_nonempty.image _))
  exact ⟨a,ha.symm⟩

omit [Nonempty ι] in
theorem threshold_sum (x : ι → ℚ) (k : ℚ) (a : ι) :
    ∑ i ∈ upper x a, (x i-threshold x k a)=k := by
  have hc : ((upper x a).card:ℚ) ≠ 0 := by exact_mod_cast (upper_card_pos x a).ne'
  simp only [sum_sub_distrib,sum_const,nsmul_eq_mul,threshold]
  field_simp
  ring

theorem project_nonneg (x : ι → ℚ) (k : ℚ) (i : ι) : 0 ≤ project x k i := le_max_left _ _

theorem project_sum (x : ι → ℚ) (k : ℚ) (hk : 0 < k) : ∑ i, project x k i=k := by
  obtain ⟨b,hb⟩ := level_attained x k
  have hlow : k ≤ ∑ i, project x k i := by
    calc
      k = ∑ i ∈ upper x b, (x i-level x k) := by rw [hb,threshold_sum]
      _ ≤ ∑ i ∈ upper x b, project x k i := sum_le_sum (fun _ _ => le_max_right _ _)
      _ ≤ ∑ i, project x k i := sum_le_sum_of_subset_of_nonneg (subset_univ _)
        (fun i _ _ => project_nonneg x k i)
  let A := univ.filter (fun i => 0 < project x k i)
  have hA : A.Nonempty := by
    by_contra h
    have hz : ∀ i, project x k i=0 := by
      intro i
      exact le_antisymm (le_of_not_gt (fun hp => h ⟨i,mem_filter.mpr ⟨mem_univ _,hp⟩⟩))
        (project_nonneg x k i)
    simp only [hz,sum_const_zero] at hlow
    exact (not_le_of_gt hk) hlow
  obtain ⟨a,ha,hmin⟩ := A.exists_min_image x hA
  have ha' : 0 < project x k a := (mem_filter.mp ha).2
  have hax : level x k < x a := by
    simpa only [project,lt_max_iff,lt_self_iff_false,false_or,sub_pos] using ha'
  have hset : A=upper x a := by
    ext i
    constructor
    · intro hi
      exact mem_filter.mpr ⟨mem_univ _,hmin i hi⟩
    · intro hi
      have hxi := (mem_filter.mp hi).2
      apply mem_filter.mpr
      exact ⟨mem_univ _,lt_max_of_lt_right (sub_pos.mpr (hax.trans_le hxi))⟩
  have hout : ∑ i, project x k i=∑ i ∈ upper x a, (x i-level x k) := by
    rw [← hset]
    calc
      _ = ∑ i ∈ A, project x k i := (sum_subset (subset_univ _) (by
        intro i _ hi
        exact le_antisymm (le_of_not_gt (fun hp => hi (mem_filter.mpr ⟨mem_univ _,hp⟩)))
          (project_nonneg x k i))).symm
      _ = _ := sum_congr rfl (fun i hi => by
        have hp : level x k < x i := by
          simpa only [project,lt_max_iff,lt_self_iff_false,false_or,sub_pos]
            using (mem_filter.mp hi).2
        exact max_eq_right (sub_nonneg.mpr hp.le))
  apply le_antisymm _ hlow
  rw [hout]
  calc
    _ ≤ ∑ i ∈ upper x a, (x i-threshold x k a) :=
      sum_le_sum (fun i _ => sub_le_sub_left (threshold_le_level x k a) (x i))
    _ = k := threshold_sum x k a

theorem project_variational (x y : ι → ℚ) (k : ℚ) (hk : 0 < k)
    (hy : ∀ i, 0 ≤ y i) (hys : ∑ i, y i=k) :
    (∑ i, (x i-project x k i)*(y i-project x k i)) ≤ 0 := by
  have hterm : ∀ i, (x i-project x k i-level x k)*(y i-project x k i) ≤ 0 := by
    intro i
    by_cases hi : x i ≤ level x k
    · have hp : project x k i=0 := max_eq_left (sub_nonpos.mpr hi)
      rw [hp,sub_zero,sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hi) (hy i)
    · have hp : project x k i=x i-level x k := max_eq_right (sub_nonneg.mpr (le_of_not_ge hi))
      rw [hp]
      have he : x i-(x i-level x k)-level x k=0 := by ring
      rw [he,zero_mul]
  have hh := sum_nonpos (fun i (_ : i ∈ univ) => hterm i)
  have hid : (∑ i, (x i-project x k i-level x k)*(y i-project x k i)) =
      (∑ i, (x i-project x k i)*(y i-project x k i)) := by
    have hz : (∑ i, (y i-project x k i))=0 := by
      rw [sum_sub_distrib,hys,project_sum x k hk,sub_self]
    calc
      _ = ∑ i, ((x i-project x k i)*(y i-project x k i)-
          level x k*(y i-project x k i)) := sum_congr rfl (fun _ _ => by ring)
      _ = _ := by rw [sum_sub_distrib,← mul_sum,hz,mul_zero,sub_zero]
  rwa [hid] at hh

theorem project_sqdist (x y : ι → ℚ) (k : ℚ) (hk : 0 < k)
    (hy : ∀ i, 0 ≤ y i) (hys : ∑ i, y i=k) :
    (∑ i, (project x k i-y i)^2) ≤ ∑ i, (x i-y i)^2 := by
  have hv := project_variational x y k hk hy hys
  have hs : 0 ≤ ∑ i, (x i-project x k i)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hid : (∑ i, (x i-y i)^2) = (∑ i, (project x k i-y i)^2) +
      (∑ i, (x i-project x k i)^2) -
      2*(∑ i, (x i-project x k i)*(y i-project x k i)) := by
    rw [← sum_add_distrib,mul_sum,← sum_sub_distrib]
    exact sum_congr rfl (fun _ _ => by ring)
  linarith

end MetricKMedian.Simplex
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_ProjectedSubgradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ProjectedSubgradient
open Finset
variable {n : ℕ} [NeZero n]

abbrev point (v : Vector ℚ n) : Fin n → ℚ := fun i => v[i.val]

def sqdist (x y : Fin n → ℚ) : ℚ := ∑ i, (x i-y i)^2

omit [NeZero n] in
theorem sqdist_nonneg (x y : Fin n → ℚ) : 0 ≤ sqdist x y :=
  sum_nonneg (fun _ _ => sq_nonneg _)

omit [NeZero n] in
@[simp] theorem point_ofFn (f : Fin n → ℚ) : point (Vector.ofFn f)=f := by
  funext i
  simp only [point,Vector.getElem_ofFn]

omit [NeZero n] in
@[simp] theorem point_ofFn_apply (f : Fin n → ℚ) (i : Fin n) : point (Vector.ofFn f) i=f i := by
  simp only [point,Vector.getElem_ofFn]

def next (k η : ℚ) (g : (Fin n → ℚ) → Fin n → ℚ) (v : Vector ℚ n) : Vector ℚ n :=
  let w := Vector.ofFn (fun i => point v i-η*g (point v) i)
  let L := Simplex.level (point w) k
  Vector.ofFn (fun i => max 0 (point w i-L))

@[simp] theorem next_apply (k η : ℚ) (g : (Fin n → ℚ) → Fin n → ℚ)
    (v : Vector ℚ n) (i : Fin n) :
    point (next k η g v) i=Simplex.project (fun a => point v a-η*g (point v) a) k i := by
  simp only [next,point_ofFn_apply,point_ofFn,Simplex.project]

def trajectory (k η : ℚ) (g : (Fin n → ℚ) → Fin n → ℚ)
    (v : Vector ℚ n) : ℕ → Vector ℚ n
  | 0 => v
  | t+1 => next k η g (trajectory k η g v t)

@[simp] theorem trajectory_zero (k η : ℚ) (g : (Fin n → ℚ) → Fin n → ℚ)
    (v : Vector ℚ n) : trajectory k η g v 0=v := rfl

@[simp] theorem trajectory_succ (k η : ℚ) (g : (Fin n → ℚ) → Fin n → ℚ)
    (v : Vector ℚ n) (t : ℕ) :
    trajectory k η g v (t+1)=next k η g (trajectory k η g v t) := rfl

def feasible (k : ℚ) (x : Fin n → ℚ) : Prop := (∀ i, 0 ≤ x i) ∧ ∑ i, x i=k

theorem trajectory_feasible (k η : ℚ) (g : (Fin n → ℚ) → Fin n → ℚ)
    (v : Vector ℚ n) (hk : 0 < k) (hv : feasible k (point v)) (t : ℕ) :
    feasible k (point (trajectory k η g v t)) := by
  cases t with
  | zero => exact hv
  | succ t =>
    constructor
    · intro i; rw [trajectory_succ,next_apply]; exact Simplex.project_nonneg _ _ _
    · simp only [trajectory_succ,next_apply]
      exact Simplex.project_sum _ _ hk

theorem next_descent (f : (Fin n → ℚ) → ℚ) (g : (Fin n → ℚ) → Fin n → ℚ)
    (k η G : ℚ) (hk : 0 < k) (hη : 0 ≤ η)
    (v : Vector ℚ n) (z : Fin n → ℚ) (hz : feasible k z)
    (hsg : f (point v)-f z ≤ ∑ i, g (point v) i*(point v i-z i))
    (hg : ∑ i, (g (point v) i)^2 ≤ G) :
    sqdist (point (next k η g v)) z ≤
      sqdist (point v) z-2*η*(f (point v)-f z)+η^2*G := by
  have hp := Simplex.project_sqdist (fun i => point v i-η*g (point v) i) z k hk hz.1 hz.2
  have hid : (∑ i, (point v i-η*g (point v) i-z i)^2)=
      sqdist (point v) z-2*η*(∑ i, g (point v) i*(point v i-z i))+
        η^2*(∑ i, (g (point v) i)^2) := by
    unfold sqdist
    rw [mul_sum,mul_sum,← sum_sub_distrib,← sum_add_distrib]
    exact sum_congr rfl (fun _ _ => by ring)
  rw [hid] at hp
  have hsg' := mul_le_mul_of_nonneg_left hsg (mul_nonneg (show (0:ℚ) ≤ 2 by norm_num) hη)
  have hg' := mul_le_mul_of_nonneg_left hg (sq_nonneg η)
  have hmain : (∑ i, (Simplex.project (fun i => point v i-η*g (point v) i) k i-z i)^2) ≤
      sqdist (point v) z-2*η*(f (point v)-f z)+η^2*G := hp.trans (by linarith)
  simpa only [sqdist,next_apply] using hmain

theorem regret (f : (Fin n → ℚ) → ℚ) (g : (Fin n → ℚ) → Fin n → ℚ)
    (k η G : ℚ) (hk : 0 < k) (hη : 0 ≤ η) (v : Vector ℚ n)
    (hv : feasible k (point v)) (z : Fin n → ℚ) (hz : feasible k z)
    (hsg : ∀ y, feasible k y → f y-f z ≤ ∑ i, g y i*(y i-z i))
    (hg : ∀ y, feasible k y → ∑ i, (g y i)^2 ≤ G) (T : ℕ) :
    2*η*(∑ t ∈ range T, (f (point (trajectory k η g v t))-f z)) ≤
      sqdist (point v) z-sqdist (point (trajectory k η g v T)) z+(T:ℚ)*η^2*G := by
  induction T with
  | zero => simp only [range_zero,sum_empty,mul_zero,trajectory_zero,sub_self,Nat.cast_zero,zero_mul,add_zero,le_refl]
  | succ T ih =>
    have ht := trajectory_feasible k η g v hk hv T
    have hd := next_descent f g k η G hk hη (trajectory k η g v T) z hz
      (hsg _ ht) (hg _ ht)
    rw [sum_range_succ,Nat.cast_add,Nat.cast_one,trajectory_succ]
    linarith

theorem exists_accurate (f : (Fin n → ℚ) → ℚ) (g : (Fin n → ℚ) → Fin n → ℚ)
    (k η G δ : ℚ) (hk : 0 < k) (hη : 0 < η) (v : Vector ℚ n)
    (hv : feasible k (point v)) (z : Fin n → ℚ) (hz : feasible k z)
    (hsg : ∀ y, feasible k y → f y-f z ≤ ∑ i, g y i*(y i-z i))
    (hg : ∀ y, feasible k y → ∑ i, (g y i)^2 ≤ G) (T : ℕ) (hT : 0 < T)
    (hiter : sqdist (point v) z+(T:ℚ)*η^2*G ≤ 2*η*(T:ℚ)*δ) :
    ∃ t ∈ range T, f (point (trajectory k η g v t)) ≤ f z+δ := by
  by_contra hn
  push Not at hn
  have hsum : (T:ℚ)*δ < ∑ t ∈ range T, (f (point (trajectory k η g v t))-f z) := by
    calc
      _ = ∑ _t ∈ range T, δ := by simp only [sum_const,card_range,nsmul_eq_mul]
      _ < _ := sum_lt_sum (fun t ht => by linarith [hn t ht])
        ⟨0,mem_range.mpr hT,by linarith [hn 0 (mem_range.mpr hT)]⟩
  have hr := regret f g k η G hk hη.le v hv z hz hsg hg T
  have hd := sqdist_nonneg (point (trajectory k η g v T)) z
  have hh := mul_lt_mul_of_pos_left hsum (mul_pos (show (0:ℚ) < 2 by norm_num) hη)
  nlinarith

end MetricKMedian.ProjectedSubgradient
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_SimplexDiameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ProjectedSubgradient
open Finset
variable {n : ℕ}

def initial [NeZero n] (k : ℚ) : Vector ℚ n := Vector.ofFn (fun i => if i=0 then k else 0)

end MetricKMedian.ProjectedSubgradient
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_TruncatedObjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset
variable {ι κ : Type} [Fintype ι] [Fintype κ]

def truncated (d : κ → ι → ℚ) (H : ℚ) (j : κ) (i : ι) : ℚ :=
  if d j i ≤ 1 then d j i else H

omit [Fintype ι] [Fintype κ] in
theorem truncated_bounds (d : κ → ι → ℚ) (H : ℚ)
    (hH : 1 ≤ H) (hd : ∀ j i, 0 ≤ d j i) (j : κ) (i : ι) :
    0 ≤ truncated d H j i ∧ truncated d H j i ≤ H := by
  unfold truncated
  split_ifs with hi
  · exact ⟨hd j i,hi.trans hH⟩
  · exact ⟨(by linarith),le_rfl⟩

end MetricKMedian.TruncatedLP
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

def gradSize (H : ℕ) : ℕ := n*(m*H)^2

def steps (r k H : ℕ) : ℕ := 8*r^2*(gradSize (n:=n) (m:=m) H)*k^2

def rate (r H : ℕ) : ℚ := 1/(2*(r:ℚ)*(gradSize (n:=n) (m:=m) H:ℚ))

theorem gradSize_pos (H : ℕ) (hH : 0 < H) : 0 < gradSize (n:=n) (m:=m) H := by
  unfold gradSize
  exact Nat.mul_pos (NeZero.pos n) (pow_pos (Nat.mul_pos (NeZero.pos m) hH) _)

theorem steps_pos (r k H : ℕ) (hr : 0 < r) (hk : 0 < k) (hH : 0 < H) :
    0 < steps (n:=n) (m:=m) r k H := by
  unfold steps
  have hg := gradSize_pos (n:=n) (m:=m) H hH
  positivity

theorem rate_pos (r H : ℕ) (hr : 0 < r) (hH : 0 < H) :
    0 < rate (n:=n) (m:=m) r H := by
  unfold rate
  exact one_div_pos.mpr (mul_pos (mul_pos (by norm_num) (by exact_mod_cast hr))
    (by exact_mod_cast gradSize_pos (n:=n) (m:=m) H hH))

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_ApproximateFractional
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

def penalty (r k : ℕ) : ℕ := 4*r*(k+1)

def loss (r k : ℕ) : ℚ := (1+1/(r:ℚ))/(penalty r k:ℚ)

theorem penalty_pos (r k : ℕ) (hr : 0 < r) : 0 < penalty r k := by
  unfold penalty
  positivity

structure FractionalData (n m : ℕ) where
  opening : Vector ℚ n
  assignment : Vector (Vector ℚ n) m

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Instance
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

@[instance_reducible] def pseudoMetric (I : Instance) : PseudoMetricSpace (Fin I.n) where
  dist i j := (I.distance i j:ℝ)
  dist_self i := by rw [(I.distance_eq_zero i i).mpr rfl, Rat.cast_zero]
  dist_comm i j := by rw [I.distance_symm i j]
  dist_triangle i j h := by exact_mod_cast I.distance_triangle i j h

theorem facilities_nonempty (I : Instance) : I.facilities.Nonempty :=
  card_pos.mp (I.k_pos.trans I.k_le)

end Instance
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_MatrixNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Normalization
open Finset
variable {m n : ℕ}

def matrixGuesses (d : Fin m → Fin n → ℚ) : Finset ℚ :=
  (univ : Finset (Fin m × Fin n)).biUnion (fun a =>
    if 0 < d a.1 a.2 then
      (range (m.size+1)).image (fun t => d a.1 a.2*(2:ℚ)^t)
    else ∅)

end MetricKMedian.Normalization
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

def FractionalData.Valid (out : FractionalData n m) (k : ℕ) : Prop :=
    (∀ i : Fin n, 0 ≤ out.opening[i.val] ∧ out.opening[i.val] ≤ 1) ∧
    (∀ (j : Fin m) (i : Fin n), 0 ≤ out.assignment[j.val][i.val] ∧
      out.assignment[j.val][i.val] ≤ out.opening[i.val]) ∧
    (∀ j : Fin m, ∑ i : Fin n, out.assignment[j.val][i.val]=1) ∧
    (∑ i : Fin n, out.opening[i.val]) ≤ (k:ℚ)+1

instance instDecidableValid (out : FractionalData n m) (k : ℕ) : Decidable (out.Valid k) :=
  by unfold FractionalData.Valid; infer_instance

def FractionalData.value (out : FractionalData n m) (d : Fin m → Fin n → ℚ) : ℚ :=
  ∑ j : Fin m, ∑ i : Fin n, out.assignment[j.val][i.val]*d j i

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalFractionalInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.Preparation
open Finset
variable {f j : ℕ}

namespace FractionalRefinement

variable (a : TruncatedLP.FractionalData f j) (k : ℕ) (ha : a.Valid k) (hj : 0<j)

def y (i : Fin f) : ℚ := a.opening[i.val]

end FractionalRefinement
end MetricKMedian.Preparation
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
open Function Finset

namespace Nearest
abbrev Entry := ℕ × (ℚ × ℚ)

def before (a b : Entry) : Bool := decide (a.2.2 < b.2.2 ∨ a.2.2=b.2.2 ∧ a.1 < b.1)
def prior (es : List Entry) (a : Entry) : ℚ := ((es.filter (fun b => before b a)).map (fun e => e.2.1)).sum
def amount (es : List Entry) (a : Entry) : ℚ := min a.2.1 (max 0 (1-prior es a))
end Nearest
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_GraphLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian

namespace GraphLaw
variable {I H : Type*} [Fintype I] [Fintype H] [DecidableEq I] [DecidableEq H]

noncomputable def edge (G : I → Finset H) (h : H) (i : I) : ℝ := if h ∈ G i then 1 else 0

end GraphLaw
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_GraphMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian

namespace GraphMoments

variable {Ω I H : Type*} [Fintype Ω] [Fintype I] [Fintype H] [DecidableEq I]

noncomputable def removedMass (g : ℝ) (X : Ω → H → I → ℝ) (ω : Ω) (h : H) : ℝ :=
  ∑ i, g*X ω h i
noncomputable def removedCost (g : ℝ) (d : I → ℝ) (X : Ω → H → I → ℝ)
    (ω : Ω) (h : H) : ℝ := ∑ i, g*d i*X ω h i
noncomputable def kernel (g : ℝ) (q : H → I → ℝ) (i t : I) : ℝ :=
  ∑ h, g*q h i*q h t

end GraphMoments
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_GraphComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.GraphComparison

noncomputable def externalMass {I H : Type*} [Fintype H] (ρ : H → ℝ) (q : I → H → ℝ) (i : I) : ℝ :=
  ∑ h, ρ h*q i h
noncomputable def externalSquare {I H : Type*} [Fintype H] (ρ : H → ℝ) (q : I → H → ℝ) (i : I) : ℝ :=
  ∑ h, ρ h*(q i h)^2
noncomputable def rowType {I H : Type*} [Fintype H] (ρ : H → ℝ) (q : I → H → ℝ) (i : I) : ℝ :=
  externalSquare ρ q i/externalMass ρ q i
noncomputable def kernel {I H : Type*} [Fintype H] (ρ : H → ℝ) (q : I → H → ℝ) (i t : I) : ℝ :=
  ∑ h, ρ h*q i h*q t h

end MetricKMedian.GraphComparison
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_GeneratorAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.GeneratorAverage
open GraphComparison GraphMoments

variable {Ω I H : Type*} [Fintype Ω] [Fintype I] [Fintype H] [DecidableEq I]

noncomputable def inside (g a f : ℝ) (d : I → ℝ) (X : Ω → I → I → ℝ) (ω : Ω) : ℝ :=
  ∑ h, g*(d h-(∑ i, g*(1-X ω h i)*max (d h-a*d i) 0)-f)
noncomputable def external (g a B V : ℝ) (bH : H → ℝ) (d : I → ℝ)
    (X : Ω → H → I → ℝ) (ω : Ω) : ℝ :=
  ∑ h, g*(removedMass g X ω h*bH h-a*removedCost g d X ω h-
    B*removedMass g X ω h*(V-removedCost g d X ω h))

end MetricKMedian.GeneratorAverage
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_GroupCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.GroupCap
open Finset
variable {F E : Type*}

noncomputable def cap (R : ℝ) (d : F → ℝ) (O : Finset F) : ℝ := O.fold min (5*R) d

end MetricKMedian.GroupCap
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_SupplierListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset
abbrev BTable := List (List Bool)
end MetricKMedian.Preparation.RationalSuppliers.Program
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
open Finset

def insertData (x : List ℚ × ℚ) : List ℚ :=
  x.1.filter (fun a => decide (a<x.2)) ++ x.2::x.1.filter (fun a => decide (x.2<a))
end MetricKMedian.RationalSortProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_SplitListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.Preparation.RationalSplitting.Program
open Finset
abbrev Raw := List ℚ × List (List ℚ)
end MetricKMedian.Preparation.RationalSplitting.Program
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
open Finset
abbrev Matrix := List (List ℚ)
abbrev Raw := List ℚ × (Matrix × (Matrix × Matrix))
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

def indexedDistance (I : Instance) (j : Fin I.clients.card) (i : Fin I.facilities.card) : ℚ :=
  I.distance (I.clients.orderEmbOfFin rfl j) (I.facilities.orderEmbOfFin rfl i)

theorem indexedDistance_nonneg (I : Instance) : ∀ j i, 0 ≤ I.indexedDistance j i :=
  fun _ _ => I.distance_nonneg _ _

end Instance
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_UnitGeometryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Preparation.RationalUnitInput.Program
open Finset

def pickRows {α : Type} [Inhabited α] (x : List (List α) × List ℕ) : List (List α) :=
  x.2.map (fun i => x.1[i]?.getD [])
end MetricKMedian.Preparation.RationalUnitInput.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_InstanceParserProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.InputParser
open Finset
 theorem flatten_ofFn {n : ℕ} (d : Fin n → Fin n → ℚ) :
    (List.ofFn (fun i => List.ofFn (d i))).flatten=
      List.ofFn (fun k : Fin (n*n) => d (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) := by
  symm
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hij : i.val*n+j.val<n*n := by
    calc
      i.val*n+j.val < i.val*n+n := Nat.add_lt_add_left j.isLt _
      _ = (i.val+1)*n := by simp only [Nat.add_mul,Nat.one_mul]
      _ ≤ n*n := Nat.mul_le_mul_right n i.isLt
  have he : (⟨i.val*n+j.val, hij⟩ : Fin (n*n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext; change _=j.val+n*i.val; ac_rfl
  rw [he]
  exact congrArg (fun p : Fin n × Fin n => d p.1 p.2) (finProdFinEquiv.symm_apply_apply (i,j))
end MetricKMedian.InputParser
end

end OAI
end


