-- Prove2me | Definitions.Def_OAIQ053K021
-- name    : OAIQ053K021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:57:12.3795+00:00
-- url     : https://prove2.me/theorems/1a1ed28e-a753-4bf4-8784-57efd1d64321
-- title:
--   Definitions bundle OAIQ053K021 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 24 declarations of OpenAI's Lean: 3 definitions and 21 theorems. The definitions and types are `OAI.MetricKMedian.PCP.Amplifier.Label`, `OAI.MetricKMedian.rationalCost`, `OAI.MetricKMedian.rationalNearest`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Amplification_Amplifier`, `KMedian_Geometry_RationalInstanceCost`, `KMedian_Instance`, `KMedian_Optimization_ApproximateFractional`, `KMedian_Optimization_ApproximateLPSelection`, `KMedian_Optimization_MatrixNormalization`, `KMedian_Optimization_ProjectedSubgradient`, `KMedian_Optimization_RationalArgmin`, `KMedian_Optimization_SimplexDiameter`, `KMedian_Optimization_SimplexProjection`, `KMedian_Optimization_TruncatedOptimization`, `KMedian_Optimization_TruncatedRepair`, `KMedian_Reduction_NormalizationGuesses`.
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundles `OAIQ053K000`, `OAIQ053K001`, `OAIQ053K002`, `OAIQ053K003`, `OAIQ053K006`, `OAIQ053K007` and `OAIQ053K008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K033`, `OAIQ053K034` and `OAIQ053K037`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K000
import Definitions.Def_OAIQ053K001
import Definitions.Def_OAIQ053K002
import Definitions.Def_OAIQ053K003
import Definitions.Def_OAIQ053K006
import Definitions.Def_OAIQ053K007
import Definitions.Def_OAIQ053K008

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_Amplifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAmplifier

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace Amplifier
abbrev Label := IncidenceReduction.Label

end Amplifier
end MetricKMedian.PCP

end Inline_PCPAmplifier

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Instance
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

theorem mem_feasible (I : Instance) (S : Finset (Fin I.n)) :
    S ∈ feasibleSets I ↔ S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k := by
  simp only [feasibleSets,mem_filter,mem_powerset]

end Instance
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalInstanceCost
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset

def rationalNearest (I : Instance) (j : Fin I.n) (S : Finset (Fin I.n)) : ℚ :=
  if h : S.Nonempty then
    (S.image (I.distance j)).min' (h.image _)
  else 0

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
-- module Solutions.OAIQ053_KM.KMedian_Optimization_SimplexProjection
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
-- module Solutions.OAIQ053_KM.KMedian_Optimization_ProjectedSubgradient
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
-- module Solutions.OAIQ053_KM.KMedian_Optimization_SimplexDiameter
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

theorem diameter_sq (k : ℚ) (x y : Fin n → ℚ)
    (hx : feasible k x) (hy : feasible k y) : sqdist x y ≤ 2*k^2 := by
  have hxx := sum_sq_le_sq_sum_of_nonneg (s:=(univ:Finset (Fin n))) (fun i _ => hx.1 i)
  have hyy := sum_sq_le_sq_sum_of_nonneg (s:=(univ:Finset (Fin n))) (fun i _ => hy.1 i)
  rw [hx.2] at hxx
  rw [hy.2] at hyy
  have hper : ∀ i, (x i-y i)^2 ≤ (x i)^2+(y i)^2 := by
    intro i
    nlinarith [mul_nonneg (hx.1 i) (hy.1 i)]
  have hh := sum_le_sum (fun i (_ : i ∈ (univ:Finset (Fin n))) => hper i)
  rw [sum_add_distrib] at hh
  unfold sqdist
  linarith

end MetricKMedian.ProjectedSubgradient
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_TruncatedOptimization
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

theorem iteration_bound (r k H : ℕ) (hr : 0 < r) (hH : 0 < H)
    (v : Vector ℚ n) (z : Fin n → ℚ)
    (hv : feasible (k:ℚ) (point v)) (hz : feasible (k:ℚ) z) :
    sqdist (point v) z+(steps (n:=n) (m:=m) r k H:ℚ)*(rate (n:=n) (m:=m) r H)^2*
      (gradSize (n:=n) (m:=m) H:ℚ) ≤
      2*rate (n:=n) (m:=m) r H*(steps (n:=n) (m:=m) r k H:ℚ)*(1/(r:ℚ)) := by
  have hD := diameter_sq (k:ℚ) (point v) z hv hz
  have hr0 : (r:ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  have hg0 : (gradSize (n:=n) (m:=m) H:ℚ) ≠ 0 := by
    exact_mod_cast (gradSize_pos (n:=n) (m:=m) H hH).ne'
  have hsteps : (steps (n:=n) (m:=m) r k H:ℚ)=
      8*(r:ℚ)^2*(gradSize (n:=n) (m:=m) H:ℚ)*(k:ℚ)^2 := by
    simp only [steps,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have hnoise : (steps (n:=n) (m:=m) r k H:ℚ)*(rate (n:=n) (m:=m) r H)^2*
      (gradSize (n:=n) (m:=m) H:ℚ)=2*(k:ℚ)^2 := by
    rw [hsteps,rate]
    field_simp
    ring
  have hgain : 2*rate (n:=n) (m:=m) r H*(steps (n:=n) (m:=m) r k H:ℚ)*(1/(r:ℚ))=
      8*(k:ℚ)^2 := by
    rw [hsteps,rate]
    field_simp
  rw [hnoise,hgain]
  nlinarith [sq_nonneg (k:ℚ)]

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_TruncatedRepair
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

theorem nearMass_lower (d x : κ → ι → ℚ) (H ρ : ℚ)
    (hH : 1 ≤ H) (hd : ∀ j i, 0 ≤ d j i) (hx : ∀ j i, 0 ≤ x j i)
    (hs : ∀ j, ∑ i, x j i=1)
    (hcost : (∑ j, ∑ i, x j i*truncated d H j i) ≤ ρ*H) (j : κ) :
    1-ρ ≤ nearMass d x j := by
  classical
  have hc : ∀ j, 0 ≤ ∑ i, x j i*truncated d H j i := fun j =>
    sum_nonneg (fun i _ => mul_nonneg (hx j i) (truncated_bounds d H hH hd j i).1)
  have hterm : ∀ i, H*(x j i-nearWeight d x j i) ≤ x j i*truncated d H j i := by
    intro i
    unfold nearWeight truncated
    split_ifs
    · simpa only [sub_self,mul_zero] using mul_nonneg (hx j i) (hd j i)
    · simp only [sub_zero]; exact (mul_comm _ _).le
  have hf : H*(1-nearMass d x j) ≤ ρ*H := by
    calc
      _ = ∑ i, H*(x j i-nearWeight d x j i) := by
        rw [← mul_sum,sum_sub_distrib,hs]; rfl
      _ ≤ ∑ i, x j i*truncated d H j i := sum_le_sum (fun i _ => hterm i)
      _ ≤ ∑ j, ∑ i, x j i*truncated d H j i := single_le_sum (fun j _ => hc j) (mem_univ j)
      _ ≤ _ := hcost
  nlinarith

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_ApproximateFractional
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

theorem penalty_pos (r k : ℕ) (hr : 0 < r) : 0 < penalty r k := by
  unfold penalty
  positivity

theorem penalty_one (r k : ℕ) (hr : 0 < r) : (1:ℚ) ≤ penalty r k := by
  exact_mod_cast penalty_pos r k hr

theorem loss_bounds (r k : ℕ) (hr : 0 < r) (hk : 0 < k) :
    0 < loss r k ∧ loss r k ≤ 1/(4*(r:ℚ)) ∧ loss r k < 1 ∧
      loss r k*((k:ℚ)+1) ≤ 1 := by
  have hrq : (1:ℚ) ≤ r := by exact_mod_cast hr
  have hkq : (1:ℚ) ≤ k := by exact_mod_cast hk
  have hrp : (0:ℚ) < r := by linarith
  have hkp : (0:ℚ) < (k:ℚ)+1 := by linarith
  have ht : 1/(r:ℚ) ≤ 1 := (div_le_one hrp).mpr hrq
  have hH : (penalty r k:ℚ)=4*(r:ℚ)*((k:ℚ)+1) := by
    simp only [penalty,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
  have hpos : 0 < loss r k := by
    unfold loss
    exact div_pos (by positivity) (by exact_mod_cast penalty_pos r k hr)
  have hb : loss r k ≤ 1/(4*(r:ℚ)) := by
    unfold loss
    rw [hH]
    apply (div_le_div_iff₀ (mul_pos (by positivity) hkp) (by positivity)).mpr
    nlinarith
  refine ⟨hpos,hb,?_,?_⟩
  · have hh : 1/(4*(r:ℚ)) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    exact hb.trans_lt hh
  · unfold loss
    rw [hH,div_mul_eq_mul_div]
    apply (div_le_one (by positivity)).mpr
    nlinarith

omit [NeZero n] [NeZero m] in
theorem repair_error (r k : ℕ) (hr : 0 < r) (hk : 0 < k) (s : ℚ) (hs : 1/2 ≤ s) :
    (s+1/(r:ℚ))/(1-loss r k) ≤ (1+3/(r:ℚ))*s := by
  obtain ⟨_,hρ,hρ1,_⟩ := loss_bounds r k hr hk
  have hrq : (1:ℚ) ≤ r := by exact_mod_cast hr
  have hrp : (0:ℚ) < r := by linarith
  let t : ℚ := 1/(r:ℚ)
  have ht : 0 ≤ t := le_of_lt (one_div_pos.mpr hrp)
  have ht1 : t ≤ 1 := (div_le_one hrp).mpr hrq
  have hρt : loss r k ≤ t/4 := by
    convert hρ using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [t]
    ring
  have hp := mul_le_mul_of_nonneg_right hρt (by linarith : 0 ≤ 1+3*t)
  have hsq : t*t ≤ t := by nlinarith
  have hp' : loss r k*(1+3*t) ≤ t := by nlinarith
  have hs0 : 0 ≤ s := by linarith
  have hps := mul_le_mul_of_nonneg_right hp' hs0
  apply (div_le_iff₀ (sub_pos.mpr hρ1)).mpr
  have he : 3/(r:ℚ)=3*t := by dsimp [t]; ring
  rw [he]
  change s+t ≤ (1+3*t)*s*(1-loss r k)
  nlinarith [mul_nonneg ht (show 0 ≤ 2*s-1 by linarith)]

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_NormalizationGuesses
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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
-- module Solutions.OAIQ053_KM.KMedian_Optimization_MatrixNormalization
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
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

theorem matrixGoodGuess (d : Fin m → Fin n → ℚ) (hd : ∀ j i, 0 ≤ d j i)
    (a : Fin m → Fin n) (hc : 0 < ∑ j, d j (a j)) :
    ∃ B ∈ matrixGuesses d, 0 < B ∧
      1/2 ≤ (∑ j, d j (a j))/B ∧ (∑ j, d j (a j))/B ≤ 1 := by
  have hJ : (univ : Finset (Fin m)).Nonempty := by
    by_contra h
    have he := not_nonempty_iff_eq_empty.mp h
    rw [he,sum_empty] at hc
    exact lt_irrefl 0 hc
  let A := univ.image (fun j => d j (a j))
  have hA : A.Nonempty := hJ.image _
  obtain ⟨j,_,he⟩ := mem_image.mp (max'_mem A hA)
  have hmax : ∀ b : Fin m, d b (a b) ≤ d j (a j) := by
    intro b
    rw [he]
    exact le_max' A _ (mem_image_of_mem _ (mem_univ b))
  have hupper : (∑ b, d b (a b)) ≤ (m:ℚ)*d j (a j) := by
    calc
      _ ≤ ∑ _b : Fin m, d j (a j) := sum_le_sum (fun b _ => hmax b)
      _ = _ := by simp
  have hpos : 0 < d j (a j) := by
    by_contra h
    have hz : d j (a j)=0 := le_antisymm (le_of_not_gt h) (hd j (a j))
    rw [hz,mul_zero] at hupper
    exact (not_lt_of_ge hupper) hc
  have hl : d j (a j) ≤ ∑ b, d b (a b) :=
    single_le_sum (fun b _ => hd b (a b)) (mem_univ j)
  have hn : (m:ℚ) ≤ (2:ℚ)^m.size := by
    exact_mod_cast ((Nat.size_le).mp (le_refl m.size)).le
  have hcu : (∑ b, d b (a b)) ≤ d j (a j)*(2:ℚ)^m.size :=
    hupper.trans (by nlinarith only [mul_le_mul_of_nonneg_right hn hpos.le])
  obtain ⟨t,ht,h1,h2⟩ := dyadic_bracket _ _ m.size hpos hl hcu
  let B := d j (a j)*(2:ℚ)^t
  have hB : 0 < B := mul_pos hpos (by positivity)
  refine ⟨B,mem_biUnion.mpr ⟨(j,a j),mem_univ _,?_⟩,hB,?_,?_⟩
  · simp only [ite_eq_left hpos]
    exact mem_image.mpr ⟨t,mem_range.mpr (by omega),rfl⟩
  · apply (le_div_iff₀ hB).mpr
    change 1/2*B ≤ _
    change B ≤ 2*(∑ b, d b (a b)) at h2
    linarith
  · exact (div_le_one hB).mpr h1

end MetricKMedian.Normalization
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_RationalArgmin
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset

theorem rationalArgmin_spec (A : Finset ℚ) (f : ℚ → ℚ) (hA : A.Nonempty) :
    rationalArgmin A f ∈ A ∧ ∀ t ∈ A, f (rationalArgmin A f) ≤ f t := by
  let v := (A.image f).min' (hA.image f)
  let B := A.filter (fun t => f t=v)
  have hB : B.Nonempty := by
    obtain ⟨t,ht,he⟩ := mem_image.mp (min'_mem (A.image f) (hA.image f))
    exact ⟨t,mem_filter.mpr ⟨ht,he⟩⟩
  have heq : rationalArgmin A f=B.min' hB := by
    simp only [rationalArgmin,dite_eq_left hA]
    change (if h : B.Nonempty then B.min' h else 0)=_
    rw [dite_eq_left hB]
  rw [heq]
  obtain ⟨h1,h2⟩ := mem_filter.mp (min'_mem B hB)
  refine ⟨h1,?_⟩
  intro t ht
  rw [h2]
  exact min'_le (A.image f) _ (mem_image_of_mem f ht)

end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_ApproximateLPSelection
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

omit [NeZero n] [NeZero m] in
theorem value_div (out : FractionalData n m) (d : Fin m → Fin n → ℚ) (B : ℚ) :
    out.value (fun j i => d j i/B)=out.value d/B := by
  simp only [FractionalData.value,mul_div_assoc,sum_div]

end MetricKMedian.TruncatedLP
end
end

end OAI
end


