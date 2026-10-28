-- Prove2me | Definitions.Def_OAIQ035K022
-- name    : OAIQ035K022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:57:18.241982+00:00
-- url     : https://prove2.me/theorems/931b84de-f4c0-4613-a966-9345870cdf75
-- title:
--   Definitions bundle OAIQ035K022 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 25 declarations of OpenAI's Lean: 7 definitions and 18 theorems. The definitions and types are `OAI.MetricKMedian.LPBinary.Repair.weights`, `OAI.MetricKMedian.RationalLastFraction.endpoint`, `OAI.MetricKMedian.RationalLastFraction.pick`, `OAI.MetricKMedian.RationalLastFraction.probability`, `OAI.MetricKMedian.RationalSignedTerminal.state`, `OAI.MetricKMedian.SparseBernoulli.target`, `OAI.MetricKMedian.SparseGridRounding.count`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Geometry_RationalFractionalInput`, `KMedian_Optimization_ApproximateFractional`, `KMedian_Optimization_ApproximateLPSelection`, `KMedian_Optimization_ApproximationListProgram`, `KMedian_Optimization_MatrixNormalization`, `KMedian_Optimization_SimplexDiameter`, `KMedian_Optimization_TruncatedOptimization`, `KMedian_Optimization_TruncatedRepair`, `KMedian_Rounding_MarginalRounding`, `KMedian_Rounding_RationalLastFraction`, `KMedian_Rounding_RationalSignedStep`, `KMedian_Rounding_RationalSignedTerminal`, `KMedian_Sparse_SparseBernoulliFeatures`, `KMedian_Sparse_SparseGridRounding`, `KMedian_Sparse_SparseTargetSubset`.
--
--   **Imports.** It imports the bundles `OAIQ035K001`, `OAIQ035K002`, `OAIQ035K005`, `OAIQ035K006`, `OAIQ035K008`, `OAIQ035K009` and `OAIQ035K010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K032`, `OAIQ035K033`, `OAIQ035K034`, `OAIQ035K035`, `OAIQ035K036` and `OAIQ035K062`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K001
import Definitions.Def_OAIQ035K002
import Definitions.Def_OAIQ035K005
import Definitions.Def_OAIQ035K006
import Definitions.Def_OAIQ035K008
import Definitions.Def_OAIQ035K009
import Definitions.Def_OAIQ035K010

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
-- module Solutions.OAIQ035_KM.KMedian_Optimization_TruncatedRepair
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

theorem repaired_spec (d x : κ → ι → ℚ) (y : ι → ℚ) (H ρ k : ℚ)
    (hH : 1 ≤ H) (hρ : ρ < 1) (hkρ : ρ*(k+1) ≤ 1)
    (hd : ∀ j i, 0 ≤ d j i) (hy : ∀ i, 0 ≤ y i)
    (hx : ∀ j i, 0 ≤ x j i ∧ x j i ≤ y i)
    (hs : ∀ j, ∑ i, x j i=1) (hybudget : ∑ i, y i ≤ k)
    (hcost : (∑ j, ∑ i, x j i*truncated d H j i) ≤ ρ*H) :
    (∀ i, 0 ≤ repairedOpening y ρ i ∧ repairedOpening y ρ i ≤ 1) ∧
    (∀ j i, 0 ≤ repairedAssignment d x j i ∧
      repairedAssignment d x j i ≤ repairedOpening y ρ i) ∧
    (∀ j, ∑ i, repairedAssignment d x j i=1) ∧
    (∑ i, repairedOpening y ρ i) ≤ k+1 ∧
    (∑ j, ∑ i, repairedAssignment d x j i*d j i) ≤
      (∑ j, ∑ i, x j i*truncated d H j i)/(1-ρ) := by
  classical
  have hρp : 0 < 1-ρ := sub_pos.mpr hρ
  have hx0 : ∀ j i, 0 ≤ x j i := fun j i => (hx j i).1
  have hm : ∀ j, 1-ρ ≤ nearMass d x j := nearMass_lower d x H ρ hH hd hx0 hs hcost
  have hmp : ∀ j, 0 < nearMass d x j := fun j => hρp.trans_le (hm j)
  have hw : ∀ j i, 0 ≤ nearWeight d x j i := nearWeight_nonneg d x hx0
  have hwy : ∀ j i, nearWeight d x j i ≤ y i := fun j i =>
    (nearWeight_le d x hx0 j i).trans (hx j i).2
  have hwm : ∀ j i, nearWeight d x j i ≤ nearMass d x j := fun j i =>
    single_le_sum (fun a _ => hw j a) (mem_univ i)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i
    exact ⟨le_min (by norm_num) (div_nonneg (hy i) hρp.le),min_le_left _ _⟩
  · intro j i
    refine ⟨div_nonneg (hw j i) (hmp j).le,le_min ?_ ?_⟩
    · exact (div_le_one (hmp j)).mpr (hwm j i)
    · calc
        _ ≤ nearWeight d x j i/(1-ρ) := div_le_div_of_nonneg_left (hw j i) hρp (hm j)
        _ ≤ _ := div_le_div_of_nonneg_right (hwy j i) hρp.le
  · intro j
    simp only [repairedAssignment,← sum_div]
    exact div_self (hmp j).ne'
  · calc
      _ ≤ ∑ i, y i/(1-ρ) := sum_le_sum (fun _ _ => min_le_right _ _)
      _ = (∑ i, y i)/(1-ρ) := (sum_div _ _ _).symm
      _ ≤ k/(1-ρ) := div_le_div_of_nonneg_right hybudget hρp.le
      _ ≤ k+1 := (div_le_iff₀ hρp).mpr (by nlinarith)
  · have hterm : ∀ j i, repairedAssignment d x j i*d j i ≤ x j i*truncated d H j i/(1-ρ) := by
      intro j i
      have hc : nearWeight d x j i*d j i ≤ x j i*truncated d H j i := by
        unfold nearWeight truncated
        split_ifs
        · exact le_rfl
        · simpa only [zero_mul] using mul_nonneg (hx0 j i) (by linarith : 0 ≤ H)
      calc
        _ = (nearWeight d x j i*d j i)/nearMass d x j := by unfold repairedAssignment; ring
        _ ≤ (nearWeight d x j i*d j i)/(1-ρ) :=
          div_le_div_of_nonneg_left (mul_nonneg (hw j i) (hd j i)) hρp (hm j)
        _ ≤ _ := div_le_div_of_nonneg_right hc hρp.le
    calc
      _ ≤ ∑ j, ∑ i, x j i*truncated d H j i/(1-ρ) :=
        sum_le_sum (fun j _ => sum_le_sum (fun i _ => hterm j i))
      _ = _ := by simp only [← sum_div]

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

omit [NeZero n] [NeZero m] in
theorem value_div (out : FractionalData n m) (d : Fin m → Fin n → ℚ) (B : ℚ) :
    out.value (fun j i => d j i/B)=out.value d/B := by
  simp only [FractionalData.value,mul_div_assoc,sum_div]

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

include ha hj in
theorem mass_one : 1≤∑ i, y a i := by
  let c : Fin j := ⟨0,hj⟩
  calc
    1 = ∑ i : Fin f, a.assignment[c.val][i.val] := (ha.2.2.1 c).symm
    _ ≤ ∑ i, y a i := sum_le_sum (fun i _ => (ha.2.1 c i).2)

end FractionalRefinement
end MetricKMedian.Preparation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_ApproximationListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Repair
def weights (ds xs : Row) : Row := (ds.zip xs).map (fun p => if p.1 ≤ 1 then p.2 else 0)
end Repair
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_MarginalRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.MarginalRounding

variable {I : Type*} [Fintype I]

theorem nonfractional_integral {p : I → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {i : I} (hi : i ∉ fractional p) : p i=0 ∨ p i=1 := by
  simp only [mem_fractional, not_and_or, not_lt] at hi
  rcases hi with hi | hi
  · exact Or.inl (le_antisymm hi (hp i))
  · exact Or.inr (le_antisymm (hp1 i) hi)

end MetricKMedian.MarginalRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalLastFraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalLastFraction
open Finset RationalWeightedStep
variable {n : ℕ}

def pick (p : Vector ℚ n) (h : (fractional p).Nonempty) : Fin n := (fractional p).min' h

theorem pick_mem (p : Vector ℚ n) (h : (fractional p).Nonempty) : pick p h ∈ fractional p :=
  min'_mem _ _

def probability (p : Vector ℚ n) : ℚ :=
  if h : (fractional p).Nonempty then point p (pick p h) else 0

def endpoint (p : Vector ℚ n) (b : Fin 2) : Vector ℚ n :=
  if h : (fractional p).Nonempty then
    Vector.ofFn (fun k => if k=pick p h then (if b=0 then 1 else 0) else point p k)
  else p

theorem probability_unit (p : Vector ℚ n) : 0 ≤ probability p ∧ probability p ≤ 1 := by
  unfold probability
  split_ifs with h
  · have hh := (mem_filter.mp (pick_mem p h)).2
    exact ⟨hh.1.le,hh.2.le⟩
  · exact ⟨le_rfl,by norm_num⟩

end MetricKMedian.RationalLastFraction
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalSignedStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalSignedStep
open Finset RationalWeightedStep
variable {n : ℕ}

theorem inactive (u : Fin n → ℚ) (p : Vector ℚ n) (h : ¬Active u p) :
    ∀ i∈fractional p, ∀ j∈fractional p, i≠j → ¬0<u i*u j := by
  intro i hi j hj hij hs
  apply h
  refine ⟨finProdFinEquiv (i,j),?_⟩
  simp only [pairs,mem_filter,mem_univ,true_and,Equiv.symm_apply_apply]
  exact ⟨hi,hj,hij,hs⟩

end MetricKMedian.RationalSignedStep
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBernoulliFeatures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

theorem used_without (f : Fin d → Fin (n+1)) (i : Fin n) :
    used (without f i)=(used f).erase i := by
  ext x
  simp only [used,mem_filter,mem_univ,true_and,mem_erase]
  constructor
  · rintro ⟨a,ha⟩
    dsimp only [without] at ha
    split_ifs at ha with h
    · exact False.elim ((Nat.ne_of_gt x.isLt) ha)
    · refine ⟨?_,a,ha⟩
      intro he
      exact h (ha.trans (congrArg Fin.val he))
  · rintro ⟨hxi,a,ha⟩
    refine ⟨a,?_⟩
    dsimp only [without]
    rw [ite_eq_right (fun h => hxi (Fin.ext (ha.symm.trans h)))]
    exact ha

def target (p : Fin n → ℚ) (t : ℕ) (f : Fin d → Fin (n+1)) : ℚ :=
  ∏ i ∈ used f, if i.val<t then p i else 0

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalSignedTerminal
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

def state (u : Fin n → ℚ) (p : Vector ℚ n) (ω : Fin n → Bool) : Vector ℚ n :=
  Vector.ofFn (fun i => if u i<0 then point p i else SparseBernoulli.flag ω i)

@[simp] theorem point_state (u : Fin n → ℚ) (p : Vector ℚ n) (ω : Fin n → Bool) (i : Fin n) :
    point (state u p ω) i=(if u i<0 then point p i else SparseBernoulli.flag ω i) := by
  simp only [state,point,Vector.getElem_ofFn,Fin.eta]

end MetricKMedian.RationalSignedTerminal
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseGridRounding
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

def count (q : Fin n → ℚ) (p : Vector ℚ n) (i : Fin n) : ℕ :=
  base q i+if point p i=1 then 1 else 0

theorem fraction_unit (q : Fin n → ℚ) (hq : ∀ i, 0 ≤ q i) :
    ∀ i, 0 ≤ point (fraction q) i ∧ point (fraction q) i ≤ 1 := by
  intro i
  simp only [point,fraction,Vector.getElem_ofFn]
  constructor
  · exact sub_nonneg.mpr (Nat.floor_le (hq i))
  · have hh := Nat.lt_floor_add_one (q i)
    dsimp only [base]
    linarith only [hh]

end MetricKMedian.SparseGridRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseTargetSubset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseTargetSubset
open Finset RationalWeightedStep
variable {n : ℕ}

@[simp] theorem point_initial (D : Finset (Fin n)) (q : ℚ) (i : Fin n) :
    point (initial D q) i=(if i∈D then q else 0) := by
  simp only [initial,point,Vector.getElem_ofFn,Fin.eta]

end MetricKMedian.SparseTargetSubset
end
end

end OAI
end


