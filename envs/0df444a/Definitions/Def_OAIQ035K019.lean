-- Prove2me | Definitions.Def_OAIQ035K019
-- name    : OAIQ035K019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:56:04.147616+00:00
-- url     : https://prove2.me/theorems/0cac2b00-2c75-4c19-9585-3a15067bd122
-- title:
--   Definitions bundle OAIQ035K019 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 64 declarations of OpenAI's Lean: 29 definitions, 3 inductive types or structures and 32 theorems. The definitions and types are `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.Input.item`, `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.Input.items`, `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.Input.raw`, `OAI.MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram.Input.raw`, `OAI.MetricKMedian.IntegerLaw.BinaryCompression.LawData`, `OAI.MetricKMedian.RationalLaw.scaledFeatures`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.Input`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.Input.taper`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.instLinearOrderSubtypeCopyFinMemFinset`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyList.activeOrder`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyList.ordinal`, `OAI.MetricKMedian.RationalPhysicalKernel.HistoryProgram.nextCtx`, `OAI.MetricKMedian.RationalPhysicalKernel.RoundProgram.dummy`, `OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.Context`, `OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.Input`, `OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.Input.proposal`, `OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.instLinearOrderSubtypeCopyFinMemFinset`, `OAI.MetricKMedian.RationalPhysicalKernel.enumeration`, `OAI.MetricKMedian.RationalPhysicalKernel.instLinearOrderCopy`, `OAI.MetricKMedian.RationalPhysicalKernel.own`, `OAI.MetricKMedian.RoundingHeight.denominator`, `OAI.MetricKMedian.SparseGraph.ListOperation.view`, `OAI.MetricKMedian.SparseHistories.extend`, `OAI.MetricKMedian.Taper.A`, `OAI.MetricKMedian.Taper.B`, `OAI.MetricKMedian.Taper.candidates`, `OAI.MetricKMedian.Taper.inverseRadius`, `OAI.MetricKMedian.Taper.rationalMass`, `OAI.MetricKMedian.Taper.rootCandidates`, `OAI.MetricKMedian.Taper.sourceMarginals`, `OAI.MetricKMedian.TaperGraphProgram.Input.qInput`, `OAI.MetricKMedian.TaperGraphProgram.Input.raw`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Compression_CompressionListStep`, `KMedian_Compression_RationalScaling`, `KMedian_Geometry_BoundFreeCompression`, `KMedian_Geometry_ComputedRationalCompression`, `KMedian_Geometry_GraphListOperations`, `KMedian_Preparation_PreparedScanProgram`, `KMedian_Process_CopyGraphProgram`, `KMedian_Process_CopyListEncoding`, `KMedian_Process_PhysicalBatchUpdateProgram`, `KMedian_Process_PhysicalHistoriesProgram`, `KMedian_Process_PhysicalRoundProgram`, `KMedian_Process_RoundCountsProgram`, `KMedian_Process_RoundingCoordinateHeight`, `KMedian_Process_TaperGraphProgram`, `KMedian_Process_TaperReindex`, `KMedian_Rounding_RationalPhysicalKernel`, `KMedian_Rounding_RationalSignedStep`, `KMedian_Rounding_RationalTaper`, `KMedian_Rounding_RationalTaperAffine`, `KMedian_Rounding_RationalTaperCandidates`, `KMedian_Rounding_RationalTaperData`, `KMedian_Rounding_SignedGridInvariant`, `KMedian_Rounding_WeightedGridInvariant`, `KMedian_Rounding_WeightedRounding`, `KMedian_Sparse_SparseHistories`.
--
--   **Imports.** It imports the bundles `OAIQ035K000`, `OAIQ035K001`, `OAIQ035K002`, `OAIQ035K003`, `OAIQ035K004`, `OAIQ035K005` and `OAIQ035K006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K029`, `OAIQ035K030`, `OAIQ035K031`, `OAIQ035K032`, `OAIQ035K036` and `OAIQ035K062`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K000
import Definitions.Def_OAIQ035K001
import Definitions.Def_OAIQ035K002
import Definitions.Def_OAIQ035K003
import Definitions.Def_OAIQ035K004
import Definitions.Def_OAIQ035K005
import Definitions.Def_OAIQ035K006

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_RationalScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.RationalScaling
open Finset
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
theorem denominator_bound (q : Ω → ℚ) (L : ℕ)
    (hq : ∀ i, ((q i).den:ℤ) ≤ 2^L) :
    denominator q ≤ (2:ℤ)^(L*Fintype.card Ω) := by
  calc
    _ ≤ ∏ _i : Ω, (2:ℤ)^L := prod_le_prod (fun index _ => by positivity) (fun index _ => hq index)
    _ = _ := by simp only [prod_const,card_univ,← pow_mul]

end MetricKMedian.RationalScaling

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_ComputedRationalCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.RationalLaw
open Finset

def scaledFeatures {n d : ℕ} (v : Fin n → Fin d → ℚ) : Fin n → Fin d → ℤ :=
  let M := Vector.ofFn (fun i => Vector.ofFn (fun j => RationalScaling.numerator (fun i => v i j) i))
  fun i j => M[i.val][j.val]

@[simp] theorem scaledFeatures_eq {n d : ℕ} (v : Fin n → Fin d → ℚ)
    (i : Fin n) (j : Fin d) :
    scaledFeatures v i j=RationalScaling.numerator (fun i => v i j) i := by
  simp only [scaledFeatures,Vector.getElem_ofFn]

end MetricKMedian.RationalLaw

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

theorem exists_rational_feature_bound {n d : ℕ} (v : Fin n → Fin d → ℚ) :
    ∃ L : ℕ, (∀ i j, |(v i j).num| ≤ (2:ℤ)^L) ∧
      (∀ i j, ((v i j).den:ℤ) ≤ (2:ℤ)^L) := by
  obtain ⟨A,hA⟩ := exists_feature_bound (fun i j => (v i j).num)
  obtain ⟨B,hB⟩ := exists_feature_bound (fun i j => ((v i j).den:ℤ))
  refine ⟨max A B,fun i j => (hA i j).trans ?_,fun i j => ?_⟩
  · exact pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
  · exact (le_abs_self _).trans ((hB i j).trans
      (pow_le_pow_right₀ (by norm_num) (le_max_right _ _)))

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_CompressionListStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function Finset
abbrev LawData := ListPivot.LawData

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_WeightedRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.WeightedRounding

variable {I : Type*} [Fintype I] [DecidableEq I]
open MarginalRounding

omit [Fintype I] in
theorem move_left (p : I → ℝ) {i j : I} (hij : i ≠ j) (r t : ℝ) :
    move p i j r t i=p i+t := by simp only [move, sign, ite_true, ite_eq_right hij, sub_zero, mul_one]
omit [Fintype I] in
theorem move_right (p : I → ℝ) {i j : I} (hij : i ≠ j) (r t : ℝ) :
    move p i j r t j=p j-r*t := by simp only [move, sign, ite_eq_right hij.symm, ite_true, zero_sub]; ring
omit [Fintype I] in
theorem move_other (p : I → ℝ) {i j k : I} (hki : k ≠ i) (hkj : k ≠ j) (r t : ℝ) :
    move p i j r t k=p k := by simp only [move, sign, ite_eq_right hki, ite_eq_right hkj, sub_self, mul_zero, add_zero]

omit [Fintype I] in
theorem move_bounds {p : I → ℝ} (hp : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    {i j : I} (hij : i ≠ j) {r t : ℝ} (hr : 0 < r)
    (ht0 : -down p i j r ≤ t) (ht1 : t ≤ up p i j r) :
    (∀ k, 0 ≤ move p i j r t k) ∧ (∀ k, move p i j r t k ≤ 1) := by
  have hl1 := min_le_left (p i) ((1-p j)/r)
  have hl2 := (le_div_iff₀ hr).mp (min_le_right (p i) ((1-p j)/r))
  have hu1 := min_le_left (1-p i) (p j/r)
  have hu2 := (le_div_iff₀ hr).mp (min_le_right (1-p i) (p j/r))
  have htl := mul_le_mul_of_nonneg_left ht0 hr.le
  have htu := mul_le_mul_of_nonneg_left ht1 hr.le
  change -min (p i) ((1-p j)/r) ≤ t at ht0
  change t ≤ min (1-p i) (p j/r) at ht1
  change r * -min (p i) ((1-p j)/r) ≤ r*t at htl
  change r*t ≤ r*min (1-p i) (p j/r) at htu
  constructor <;> intro k <;> by_cases hki : k=i
  · subst k; rw [move_left p hij]; linarith only [ht0, hl1]
  · by_cases hkj : k=j
    · subst k; rw [move_right p hij]; nlinarith only [htu, hu2]
    · rw [move_other p hki hkj]; exact hp k
  · subst k; rw [move_left p hij]; linarith only [ht1, hu1]
  · by_cases hkj : k=j
    · subst k; rw [move_right p hij]; nlinarith only [htl, hl2]
    · rw [move_other p hki hkj]; exact hp1 k

theorem fractional_subset {p : I → ℝ} {i j : I}
    (hi : i ∈ fractional p) (hj : j ∈ fractional p) (r t : ℝ) :
    fractional (move p i j r t) ⊆ fractional p := by
  intro k hk
  by_cases hki : k=i
  · simpa only [hki] using hi
  by_cases hkj : k=j
  · simpa only [hkj] using hj
  simpa only [mem_fractional, move_other p hki hkj] using hk

theorem up_smaller {p : I → ℝ} {i j : I} {r : ℝ} (hr : 0 < r) (hij : i ≠ j)
    (hi : i ∈ fractional p) (hj : j ∈ fractional p) :
    (fractional (move p i j r (up p i j r))).card < (fractional p).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨fractional_subset hi hj _ _, ?_⟩
  intro heq
  rcases le_total (1-p i) (p j/r) with h | h
  · have hv : move p i j r (up p i j r) i=1 := by rw [move_left p hij, up, min_eq_left h]; ring
    have hin := heq ▸ hi
    have hnot : i ∉ fractional (move p i j r (up p i j r)) := by simp only [mem_fractional, hv]; norm_num
    exact hnot hin
  · have hv : move p i j r (up p i j r) j=0 := by
      rw [move_right p hij, up, min_eq_right h, mul_div_cancel₀ _ (ne_of_gt hr), sub_self]
    have hin := heq ▸ hj
    have hnot : j ∉ fractional (move p i j r (up p i j r)) := by simp only [mem_fractional, hv]; norm_num
    exact hnot hin

theorem down_smaller {p : I → ℝ} {i j : I} {r : ℝ} (hr : 0 < r) (hij : i ≠ j)
    (hi : i ∈ fractional p) (hj : j ∈ fractional p) :
    (fractional (move p i j r (-down p i j r))).card < (fractional p).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨fractional_subset hi hj _ _, ?_⟩
  intro heq
  rcases le_total (p i) ((1-p j)/r) with h | h
  · have hv : move p i j r (-down p i j r) i=0 := by rw [move_left p hij, down, min_eq_left h]; ring
    have hin := heq ▸ hi
    have hnot : i ∉ fractional (move p i j r (-down p i j r)) := by simp only [mem_fractional, hv]; norm_num
    exact hnot hin
  · have hv : move p i j r (-down p i j r) j=1 := by
      rw [move_right p hij, down, min_eq_right h, mul_neg, mul_div_cancel₀ _ (ne_of_gt hr)]; ring
    have hin := heq ▸ hj
    have hnot : j ∉ fractional (move p i j r (-down p i j r)) := by simp only [mem_fractional, hv]; norm_num
    exact hnot hin

theorem weighted_sum (β p : I → ℝ) {i j : I} (hj : β j ≠ 0) (t : ℝ) :
    (∑ k, β k*move p i j (β i/β j) t k)=∑ k, β k*p k := by
  simp only [move, sign, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  field_simp
  ring

end MetricKMedian.WeightedRounding
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

theorem endpoint_feasible (β : Fin n → ℚ) 
    (p : Vector ℚ n) (hp : ∀ k, 0 ≤ point p k ∧ point p k ≤ 1) (b : Fin 2) :
    ∀ k, 0 ≤ point (endpoint β p b) k ∧ point (endpoint β p b) k ≤ 1 := by
  by_cases h : Active β p
  · let a := pair β p h
    let r := β a.val.1/β a.val.2
    have hr : 0 < r := pair_ratio_pos β p h
    have hu := up_pos p _ _ r hr a.property.1 a.property.2.1
    have hd := down_pos p _ _ r hr a.property.1 a.property.2.1
    have hpr0 : ∀ k, 0 ≤ realPoint p k := fun k => by
      dsimp only [realPoint]; exact_mod_cast (hp k).1
    have hpr1 : ∀ k, realPoint p k ≤ 1 := fun k => by
      dsimp only [realPoint]; exact_mod_cast (hp k).2
    have hrr : (0:ℝ) < r := by exact_mod_cast hr
    let t := if b=0 then up p a.val.1 a.val.2 r else -down p a.val.1 a.val.2 r
    have ht0 : -down p a.val.1 a.val.2 r ≤ t := by dsimp only [t]; split_ifs <;> linarith
    have ht1 : t ≤ up p a.val.1 a.val.2 r := by dsimp only [t]; split_ifs <;> linarith
    have ht0r : -WeightedRounding.down (realPoint p) a.val.1 a.val.2 (r:ℝ) ≤ (t:ℝ) := by
      rw [← real_down,← Rat.cast_neg]; exact_mod_cast ht0
    have ht1r : (t:ℝ) ≤ WeightedRounding.up (realPoint p) a.val.1 a.val.2 (r:ℝ) := by
      rw [← real_up]; exact_mod_cast ht1
    have hh := WeightedRounding.move_bounds hpr0 hpr1 a.property.2.2.1 hrr ht0r ht1r
    rw [← real_move] at hh
    simp only [realPoint] at hh
    intro k
    simp only [endpoint,dite_eq_left h]
    exact ⟨by exact_mod_cast hh.1 k,by exact_mod_cast hh.2 k⟩
  · simpa only [endpoint,dite_eq_right h] using hp

theorem endpoint_smaller (β : Fin n → ℚ) 
    (p : Vector ℚ n) (h : Active β p) (b : Fin 2) :
    (fractional (endpoint β p b)).card < (fractional p).card := by
  let a := pair β p h
  let r := β a.val.1/β a.val.2
  have hr : (0:ℝ) < r := by exact_mod_cast pair_ratio_pos β p h
  have hi : a.val.1 ∈ MarginalRounding.fractional (realPoint p) := by
    rw [real_fractional]; exact a.property.1
  have hj : a.val.2 ∈ MarginalRounding.fractional (realPoint p) := by
    rw [real_fractional]; exact a.property.2.1
  simp only [endpoint,dite_eq_left h]
  by_cases hb : b=0
  · rw [ite_eq_left hb]
    have hh := WeightedRounding.up_smaller hr a.property.2.2.1 hi hj
    simpa only [← real_up,← real_move,real_fractional] using hh
  · rw [ite_eq_right hb]
    have hh := WeightedRounding.down_smaller hr a.property.2.2.1 hi hj
    simpa only [← real_down,← Rat.cast_neg,← real_move,real_fractional] using hh

end MetricKMedian.RationalSignedStep
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_GraphListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseGraph.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly

def view {n m : ℕ} (G : Graph n m) : Table := List.ofFn (fun i => List.ofFn (fun h => decide (h∈G i)))
end MetricKMedian.SparseGraph.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalTaperAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset

variable {I : Type*} [Fintype I]

def A (P : ℚ) (d : I → ℚ) (t : ℚ) : ℚ := ∑ i, aCoef P (d i) t

def B (P : ℚ) (d : I → ℚ) (t : ℚ) : ℚ := ∑ i, bCoef P (d i) t

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalTaperCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type*} [Fintype I]

def candidates (g P : ℚ) (d : I → ℚ) : Finset ℚ :=
  breakpoints P d ∪ ((breakpoints P d) ×ˢ (breakpoints P d)).image
    (fun p => (A P d ((p.1+p.2)/2)-1/g)/B P d ((p.1+p.2)/2))

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalTaper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type*} [Fintype I]

def rationalMass (g P : ℚ) (d : I → ℚ) (r : ℚ) : ℚ :=
  ∑ i, g*rationalMarginal P (d i) r

def rootCandidates (g P : ℚ) (d : I → ℚ) : Finset ℚ :=
  (candidates g P d).filter (fun q => 0 < q ∧ rationalMass g P d q=1)

def inverseRadius (g P : ℚ) (d : I → ℚ) : ℚ :=
  if h : (rootCandidates g P d).Nonempty then (rootCandidates g P d).max' h else 0

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalTaperData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type*} [Fintype I] [LinearOrder I]

def sourceMarginals (g P : ℚ) (d : I → ℚ) (own : Finset I) (Δ : ℕ) : I → ℚ :=
  if 1 ≤ rationalColocatedMass g d then zeroMarginal d own Δ
  else fun i => rationalMarginal P (d i) (inverseRadius g P d)

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseHistories
open Finset
variable {α : Type}

def extend (h : History α) (a : α) : History α := (a,h.1::h.2)

end MetricKMedian.SparseHistories
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalPhysicalKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset
variable {F : Type} [LinearOrder F] [Fintype F] {Δ : ℕ}

local instance instLinearOrderCopy : LinearOrder (CopyState.Copy (F := F) Δ) := copyOrder

def own (A : Finset (CopyState.Copy (F := F) Δ)) (i : A) : Finset A :=
  univ.filter (fun h => h.val.1=i.val.1)

def enumeration (A : Finset (CopyState.Copy (F := F) Δ)) : Fin A.card ≃ A :=
  (Fintype.orderIsoFinOfCardEq A (Fintype.card_coe A)).toEquiv

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyListEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.RationalPhysicalKernel.CopyList
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
variable {f Δ : ℕ}
local instance instLinearOrderCopyFin_r9715de_1 : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
abbrev activeOrder (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : LinearOrder ↥A :=
  @Subtype.instLinearOrder _ (copyOrder (F:=Fin f) (Δ:=Δ)) (·∈A)
 theorem enum_rank_strictMono (A : Finset (CopyState.Copy (F:=Fin f) Δ)) :
    StrictMono (fun i => (rank (enumeration A i).val).val) := by
  intro i j hij
  apply rank_strictMono
  exact @OrderIso.strictMono _ _ _ (activeOrder A).toPreorder
    (@Fintype.orderIsoFinOfCardEq A (activeOrder A) _ _ (Fintype.card_coe A)) i j hij

 def ordinal (A : Finset (CopyState.Copy (F:=Fin f) Δ)) :=
  @Fintype.orderIsoFinOfCardEq A (activeOrder A) _ _ (Fintype.card_coe A)
 theorem ordinal_enum (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : (ordinal A).toEquiv=enumeration A := rfl

end MetricKMedian.RationalPhysicalKernel.CopyList
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_WeightedGridInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.RationalGrid

theorem mul {D E : ℤ} {a b : ℚ} (ha : At D a) (hb : At E b) : At (D*E) (a*b) := by
  obtain ⟨A,rfl⟩ := ha
  obtain ⟨B,rfl⟩ := hb
  exact ⟨A*B,by rw [Int.cast_mul,Int.cast_mul,mul_div_mul_comm]⟩

end MetricKMedian.RationalGrid

namespace MetricKMedian.RationalWeightedStep
open Finset RationalGrid
variable {n : ℕ}

theorem up_integral (p : Vector ℚ n) (i j : Fin n) (hij : i≠j) (r : ℚ) (hr : r≠0) :
    point (move p i j r (up p i j r)) i=1 ∨ point (move p i j r (up p i j r)) j=0 := by
  rw [point_move_self _ _ _ hij,point_move_other _ _ _ hij]
  unfold up
  rcases le_total (1-point p i) (point p j/r) with h | h
  · left; rw [min_eq_left h]; ring
  · right; rw [min_eq_right h,div_mul_cancel₀ _ hr,sub_self]

end MetricKMedian.RationalWeightedStep
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_SignedGridInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.RationalSignedStep
open RationalWeightedStep RationalGrid
variable {n : ℕ}

theorem endpoint_grid (β : Fin n → ℚ) 
    (D : ℤ) (hb : ∀ i, At D (β i)) (p : Vector ℚ n)
    (hp : ∀ i, At D (β i*point p i)) (b : Fin 2) :
    ∀ i, At D (β i*point (endpoint β p b) i) := by
  by_cases h : Active β p
  · let a := pair β p h
    let i := a.val.1
    let j := a.val.2
    let r := β i/β j
    let t := if b=0 then up p i j r else -down p i j r
    let q := move p i j r t
    have hij : i≠j := a.property.2.2.1
    have hr : r≠0 := (pair_ratio_pos β p h).ne'
    have he : endpoint β p b=q := by rw [endpoint,dite_eq_left h]
    have hw : β i*point q i+β j*point q j=β i*point p i+β j*point p j :=
      move_pair_weighted β p i j hij (pair_right_ne β p h) t
    have hint : (point q i=0 ∨ point q i=1) ∨ (point q j=0 ∨ point q j=1) := by
      by_cases hb0 : b=0
      · have hh := up_integral p i j hij r hr
        simpa only [q,t,hb0,ite_true] using hh.imp (fun hi => Or.inr hi) (fun hj => Or.inl hj)
      · have hh := down_integral p i j hij r hr
        simpa only [q,t,hb0,ite_false] using hh.imp (fun hi => Or.inl hi) (fun hj => Or.inr hj)
    have hpi : At D (β i*point q i) ∧ At D (β j*point q j) := by
      rcases hint with hi | hj
      · have hai : At D (β i*point q i) := by
          rcases hi with hi | hi
          · rw [hi,mul_zero]; exact RationalGrid.zero _
          · rw [hi,mul_one]; exact hb i
        refine ⟨hai,?_⟩
        have hh := RationalGrid.sub (RationalGrid.add (hp i) (hp j)) hai
        convert hh using 1
        all_goals try with_reducible_and_instances rfl
        linarith
      · have haj : At D (β j*point q j) := by
          rcases hj with hj | hj
          · rw [hj,mul_zero]; exact RationalGrid.zero _
          · rw [hj,mul_one]; exact hb j
        refine ⟨?_,haj⟩
        have hh := RationalGrid.sub (RationalGrid.add (hp i) (hp j)) haj
        convert hh using 1
        all_goals try with_reducible_and_instances rfl
        linarith
    intro k
    rw [he]
    by_cases hki : k=i
    · subst k; exact hpi.1
    by_cases hkj : k=j
    · subst k; exact hpi.2
    simpa only [q,point_move_rest _ _ _ _ hki hkj] using hp k
  · simpa only [endpoint,dite_eq_right h] using hp

theorem endpoint_zero_weight (β : Fin n → ℚ) (p : Vector ℚ n) (b : Fin 2)
    (k : Fin n) (hk : β k=0) : point (endpoint β p b) k=point p k := by
  by_cases h : Active β p
  · let a := pair β p h
    have hi : k≠a.val.1 := by
      intro he
      have hm := a.property.2.2.2
      rw [← he,hk,zero_mul] at hm
      exact lt_irrefl _ hm
    have hj : k≠a.val.2 := by
      intro he
      have hm := a.property.2.2.2
      rw [← he,hk,mul_zero] at hm
      exact lt_irrefl _ hm
    rw [endpoint,dite_eq_left h]
    exact point_move_rest _ _ _ _ hi hj _ _
  · rw [endpoint,dite_eq_right h]

end MetricKMedian.RationalSignedStep

end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundingCoordinateHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.RationalGrid
open Binary

theorem enlarge {D : ℤ} {q : ℚ} (hq : At D q) (E : ℤ) (hE : E≠0) : At (D*E) q := by
  simpa only [Int.cast_one,mul_one] using RationalGrid.mul hq (integer E 1 hE)

theorem unit_height {D : ℤ} {q : ℚ} {H : ℕ} (hD : D≠0) (hDb : |D|≤(2:ℤ)^H)
    (hq : At D q) (hu : |q|≤1) : HasHeight q H := by
  obtain ⟨A,ha⟩ := hq
  have hDc : (D:ℚ)≠0 := by exact_mod_cast hD
  have he : (A:ℚ)=q*(D:ℚ) := ((eq_div_iff hDc).mp ha).symm
  have hA : |A|≤(2:ℤ)^H := by
    have hh : |(A:ℚ)|≤|(D:ℚ)| := by
      rw [he,abs_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hu (abs_nonneg (D:ℚ))
    exact (by exact_mod_cast hh : |A|≤|D|).trans hDb
  rw [ha]
  exact Gaussian.ratio_num_den_bound A D hD _ hA hDb

theorem divide_weight {D : ℤ} {β q : ℚ} (hD : D≠0) (hβ : β≠0) (hq : At D (β*q)) :
    At (D*β.num) q := by
  obtain ⟨A,ha⟩ := hq
  have hn : (β.num:ℚ)≠0 := by
    intro hz
    apply hβ
    rw [← Rat.num_div_den β,hz,zero_div]
  have hDc : (D:ℚ)≠0 := by exact_mod_cast hD
  refine ⟨A*β.den,?_⟩
  rw [Int.cast_mul,Int.cast_mul,Int.cast_natCast]
  apply (eq_div_iff (mul_ne_zero hDc hn)).mpr
  have hb := β.mul_den_eq_num
  calc
    q*((D:ℚ)*(β.num:ℚ)) = (β*q*(D:ℚ))*(β.den:ℚ) := by rw [← hb]; ring
    _ = (A:ℚ)*(β.den:ℚ) := by rw [(eq_div_iff hDc).mp ha]

end MetricKMedian.RationalGrid

namespace MetricKMedian.RoundingHeight
open RationalGrid RationalWeightedStep Binary
variable {n : ℕ}

def denominator (β : Fin n → ℚ) (p : Vector ℚ n) : ℤ :=
  RationalScaling.denominator β * RationalScaling.denominator (point p)

end MetricKMedian.RoundingHeight
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_TaperGraphProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.TaperGraphProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseIntegerLaw.BinarySparse

def Input.raw (x : Input) : Raw :=
  (((x.g,x.P),x.Δ),List.ofFn fun i => (List.ofFn (x.d i),List.ofFn fun h => decide (h∈x.own i)))

 theorem marginal_unit (P d r : ℚ) (hP : 0<P) :
    0≤Taper.rationalMarginal P d r ∧ Taper.rationalMarginal P d r≤1 := by
  unfold Taper.rationalMarginal
  exact ⟨le_min (by norm_num) (div_nonneg (le_max_right _ _) hP.le), min_le_left _ _⟩
 theorem source_unit {n : ℕ} (g P : ℚ) (d : Fin n → ℚ) (own : Finset (Fin n)) (Δ : ℕ) (hP : 0<P) (i : Fin n) :
    0≤Taper.sourceMarginals g P d own Δ i ∧ Taper.sourceMarginals g P d own Δ i≤1 := by
  unfold Taper.sourceMarginals
  split_ifs
  · unfold Taper.zeroMarginal; split_ifs <;> norm_num
  · exact marginal_unit _ _ _ hP

def Input.qInput (x : Input) : SparseGraph.Program.QInput :=
  ⟨x.n,x.n,(fun h i => Taper.sourceMarginals x.g x.P (x.d i) (x.own i) x.Δ h),
    fun h i => source_unit x.g x.P (x.d i) (x.own i) x.Δ x.positive h⟩
end MetricKMedian.TaperGraphProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_TaperReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                    
section
namespace MetricKMedian.Taper
open Finset
variable {I J : Type} [Fintype I] [Fintype J]

 theorem a_reindex (e : I ≃ J) (P t : ℚ) (d : J → ℚ) :
    A P (fun i => d (e i)) t=A P d t := e.sum_comp (fun j => aCoef P (d j) t)
 theorem b_reindex (e : I ≃ J) (P t : ℚ) (d : J → ℚ) :
    B P (fun i => d (e i)) t=B P d t := e.sum_comp (fun j => bCoef P (d j) t)
 theorem candidates_reindex (e : I ≃ J) (g P : ℚ) (d : J → ℚ) :
    candidates g P (fun i => d (e i))=candidates g P d := by
  simp only [candidates,breaks_reindex,a_reindex,b_reindex]
 theorem mass_reindex (e : I ≃ J) (g P t : ℚ) (d : J → ℚ) :
    rationalMass g P (fun i => d (e i)) t=rationalMass g P d t :=
  e.sum_comp (fun j => g*rationalMarginal P (d j) t)
 theorem roots_reindex (e : I ≃ J) (g P : ℚ) (d : J → ℚ) :
    rootCandidates g P (fun i => d (e i))=rootCandidates g P d := by
  simp only [rootCandidates,candidates_reindex,mass_reindex]
 theorem radius_reindex (e : I ≃ J) (g P : ℚ) (d : J → ℚ) :
    inverseRadius g P (fun i => d (e i))=inverseRadius g P d := by
  simp only [inverseRadius,roots_reindex]

variable [LinearOrder I] [LinearOrder J]
 theorem source_reindex (e : I ≃o J) (g P : ℚ) (d : J → ℚ) (own : Finset I) (Δ : ℕ) (i : I) :
    sourceMarginals g P d (own.map e.toEquiv.toEmbedding) Δ (e i)=
      sourceMarginals g P (fun j => d (e j)) own Δ i := by
  have hc : rationalColocatedMass g (fun j => d (e j))=rationalColocatedMass g d := colocated_reindex e.toEquiv g d
  have hr : inverseRadius g P (fun j => d (e j))=inverseRadius g P d := radius_reindex e.toEquiv g P d
  simp only [sourceMarginals,hc,hr]
  split_ifs
  · exact zeroMarginal_reindex e d own Δ i
  · rfl
end MetricKMedian.Taper
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyGraphProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.RationalPhysicalKernel.CopyGraphProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
open CopyList

structure Input where
  f : ℕ
  Δ : ℕ
  d : Fin f → Fin f → ℚ
  g : ℚ
  P : ℚ
  positive : 0<P
  A : Finset (CopyState.Copy (F:=Fin f) Δ)

local instance instLinearOrderSubtypeCopyFinMemFinset {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : LinearOrder ↥A := activeOrder A

def Input.taper (x : Input) : TaperGraphProgram.Input where
  n := x.A.card
  d := fun i h => x.d (enumeration x.A i).val.1 (enumeration x.A h).val.1
  own := fun i => (own x.A (enumeration x.A i)).map (enumeration x.A).symm.toEmbedding
  g := x.g
  P := x.P
  Δ := x.Δ
  positive := x.positive

 theorem taper_q (x : Input) : x.taper.qInput.q =
    (fun h i => Taper.sourceMarginals x.g x.P (fun a : x.A => x.d (enumeration x.A i).val.1 a.val.1)
      (own x.A (enumeration x.A i)) x.Δ (enumeration x.A h)) := by
  funext h i
  let e := ordinal x.A
  have hm : ((own x.A (enumeration x.A i)).map (enumeration x.A).symm.toEmbedding).map e.toEquiv.toEmbedding =
      own x.A (enumeration x.A i) := by
    rw [ordinal_enum]
    ext a
    simp only [mem_map_equiv,Equiv.symm_symm,Equiv.apply_symm_apply]
  have hh := Taper.source_reindex e x.g x.P (fun a : x.A => x.d (enumeration x.A i).val.1 a.val.1)
    ((own x.A (enumeration x.A i)).map (enumeration x.A).symm.toEmbedding) x.Δ h
  rw [hm] at hh
  exact hh.symm

end MetricKMedian.RationalPhysicalKernel.CopyGraphProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalBatchUpdateProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                  
section
namespace MetricKMedian.RationalPhysicalKernel.UpdateProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset FixedBatch
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
open CopyList
local instance instLinearOrderSubtypeCopyFinMemFinset {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : LinearOrder ↥A := activeOrder A

structure Context extends CopyGraphProgram.Input where
  β : ℚ
  p : ℚ
  φ : ℚ
  hp : 0≤p
  hφ : 0≤φ
  hupper : (1+φ)*p≤1

structure Input where
  ctx : Context
  G : ctx.A → Finset ctx.A

abbrev Input.proposal (x : Input) : RationalBatchData.ProposalProgram.Input (fun c : Context => ↥c.A) where
  ctx := x.ctx
  n := x.ctx.A.card
  enum := ordinal x.ctx.A
  G := x.G
  Δ := x.ctx.Δ
  g := x.ctx.g
  b := x.ctx.β
  p := x.ctx.p
  φ := x.ctx.φ
  hp := x.ctx.hp
  hφ := x.ctx.hφ
  hupper := x.ctx.hupper

end MetricKMedian.RationalPhysicalKernel.UpdateProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalRoundProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.RationalPhysicalKernel.RoundProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table)
open CopyList UpdateProgram

def dummy : UpdateProgram.Input where
  ctx := {
    f := 0
    Δ := 0
    d := fun i => Fin.elim0 i
    g := 0
    P := 1
    positive := by norm_num
    A := ∅
    β := 0
    p := 0
    φ := 0
    hp := le_rfl
    hφ := le_rfl
    hupper := by norm_num }
  G := fun _ => ∅

end MetricKMedian.RationalPhysicalKernel.RoundProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalHistoriesProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.RationalPhysicalKernel.HistoryProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table)
open CopyList UpdateProgram

def nextCtx (x : Context) (P : ℚ) (hP : 0<P) (A : Finset (CopyState.Copy (F:=Fin x.f) x.Δ)) : Context :=
  {x with toInput := {x.toInput with P:=P,positive:=hP,A:=A}}

end MetricKMedian.RationalPhysicalKernel.HistoryProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundCountsProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open RationalPhysicalKernel CopyList
variable {τ : ℝ}
def Input.raw (x : Input) : Raw := (List.replicate x.f (),((List.ofFn (fun i => List.ofFn (x.d₀ i)),
  List.ofFn (fun c => List.ofFn (x.d c))),List.ofFn x.n))
end MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparedScanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
variable {τ : ℝ}
def Input.raw (x : Input) : Raw := ((List.replicate x.h (),List.ofFn (fun i => (x.orig i).val)),
  ((List.ofFn (fun i => List.ofFn (x.df i)),List.ofFn (fun c => List.ofFn (x.dc c))),
  (x.ns.map List.ofFn,x.budget)))

def Input.item (x : Input) (n : Fin x.f → ℕ) : RoundCountsProgram.Input :=
  ⟨x.f,x.j,(fun a b => x.df (x.orig a) (x.orig b)),(fun c a => x.dc c (x.orig a)),n⟩
def Input.items (x : Input) := x.ns.map x.item

end MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram
end

end OAI
end


