-- Prove2me | Definitions.Def_OAIQ053K027
-- name    : OAIQ053K027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:58:09.580544+00:00
-- url     : https://prove2.me/theorems/36ba5c62-2a2b-4edc-bc7d-4a1333d37fe8
-- title:
--   Definitions bundle OAIQ053K027 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 68 declarations of OpenAI's Lean: 45 definitions, 2 inductive types or structures and 21 theorems. The definitions and types are `OAI.MetricKMedian.Preparation.SupplierStars.connectionCharge`, `OAI.MetricKMedian.Preparation.SupplierStars.supplier`, `OAI.MetricKMedian.RationalPhysicalKernel.instLinearOrderCopy_1`, `OAI.MetricKMedian.RationalPhysicalKernel.rationalPhysicalCountCopyOrder`, `OAI.MetricKMedian.Reduction.CloseCenters`, `OAI.MetricKMedian.Reduction.CloseCenters.backup`, `OAI.MetricKMedian.Reduction.CloseCenters.matched`, `OAI.MetricKMedian.Reduction.CloseCenters.region`, `OAI.MetricKMedian.Reduction.Serving`, `OAI.MetricKMedian.Reduction.Serving.bad`, `OAI.MetricKMedian.Reduction.Serving.badSet`, `OAI.MetricKMedian.Reduction.Serving.good`, `OAI.MetricKMedian.Reduction.Serving.group`, `OAI.MetricKMedian.Reduction.Serving.groupCost`, `OAI.MetricKMedian.Reduction.Serving.radius`, `OAI.MetricKMedian.Reduction.Sparse`, `OAI.MetricKMedian.Reduction.closeFromServingPseudoMetric`, `OAI.MetricKMedian.Reduction.completionGeometryPseudoMetricSpace`, `OAI.MetricKMedian.Reduction.deletionGeometryPseudoMetricSpace`, `OAI.MetricKMedian.Reduction.denseBall`, `OAI.MetricKMedian.Reduction.instPseudoMetricSpaceFinN`, `OAI.MetricKMedian.Reduction.instPseudoMetricSpaceFinN_1`, `OAI.MetricKMedian.Reduction.localCompletionPseudoMetricSpace`, `OAI.MetricKMedian.Reduction.rationalCandidates`, `OAI.MetricKMedian.Reduction.rationalRegion`, `OAI.MetricKMedian.Reduction.sparseBranches`, `OAI.MetricKMedian.Reduction.sparseDeletionPseudoMetricSpace`, `OAI.MetricKMedian.Reduction.sparsificationPseudoMetricSpace`, `OAI.MetricKMedian.Reduction.sparsifyEnumerationPseudoMetricSpace`, `OAI.MetricKMedian.Reduction.witnessedRestriction`, `OAI.MetricKMedian.ScalarTransfer.N`, `OAI.MetricKMedian.ScalarTransfer.Q0`, `OAI.MetricKMedian.ScalarTransfer.Q1`, `OAI.MetricKMedian.ScalarTransfer.Y`, `OAI.MetricKMedian.ScalarTransfer.c`, `OAI.MetricKMedian.ScalarTransfer.ell`, `OAI.MetricKMedian.ScalarTransfer.stdB`, `OAI.MetricKMedian.ScalarTransfer.stdK`, `OAI.MetricKMedian.ScalarTransfer.stdL`, `OAI.MetricKMedian.ScalarTransfer.stdM` and 7 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Analysis_NormalizedTransfer`, `KMedian_Analysis_ScalarTransfer`, `KMedian_Hardness_Analysis`, `KMedian_Preparation_SupplierCharges`, `KMedian_Preparation_SupplierMap`, `KMedian_Probability_BernoulliPolynomial`, `KMedian_Process_Taper`, `KMedian_Reduction_CloseFromServing`, `KMedian_Reduction_CompletionEnumeration`, `KMedian_Reduction_CompletionGeometry`, `KMedian_Reduction_CompletionSelection`, `KMedian_Reduction_DeletionGeometry`, `KMedian_Reduction_LocalCompletion`, `KMedian_Reduction_RationalCompletion`, `KMedian_Reduction_RationalLocalChoice`, `KMedian_Reduction_Sparsification`, `KMedian_Reduction_SparsifyEnumeration`, `KMedian_Rounding_RationalPhysicalCount`, `KMedian_Rounding_RationalPhysicalGraphInstance`, `KMedian_Rounding_RationalTaper`, `KMedian_Rounding_RationalTaperAffine`, `KMedian_Rounding_RationalTaperCandidates`, `KMedian_Rounding_RationalTaperData`, `KMedian_Rounding_RationalTaperZero`, `KMedian_Sparse_SparseBundleEncoding`, `KMedian_Sparse_SparseCountStatistic`, `KMedian_Sparse_SparseDeletion`, `KMedian_Sparse_SparseGridRounding`, `KMedian_Sparse_SparsePreparedBudget`, `KMedian_Sparse_SparsePreparedLaw`, `KMedian_Sparse_SparseRescaledInner`.
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundles `OAIQ053K001`, `OAIQ053K002`, `OAIQ053K004`, `OAIQ053K005`, `OAIQ053K006`, `OAIQ053K011` and `OAIQ053K012` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K036` and `OAIQ053K037`; the statements `OAI.MetricKMedian.Certificates.Q0_actual_pos_s53`, `OAI.MetricKMedian.Certificates.Q1_actual_pos_s53`, `OAI.MetricKMedian.Certificates.Y_actual_bounds_s53`, `OAI.MetricKMedian.ScalarTransfer.first_scalar_s53` and `OAI.MetricKMedian.ScalarTransfer.linear_scalar_s53`; the proofs of `OAI.MetricKMedian.Certificates.Q0_actual_pos_s53`, `OAI.MetricKMedian.Certificates.Q1_actual_pos_s53`, `OAI.MetricKMedian.Certificates.Y_actual_bounds_s53`, `OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s53`, `OAI.MetricKMedian.ScalarTransfer.first_scalar_s53`, `OAI.MetricKMedian.ScalarTransfer.linear_scalar_s53` and `OAI.MetricKMedian.threshold`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K001
import Definitions.Def_OAIQ053K002
import Definitions.Def_OAIQ053K004
import Definitions.Def_OAIQ053K005
import Definitions.Def_OAIQ053K006
import Definitions.Def_OAIQ053K011
import Definitions.Def_OAIQ053K012

section
-- module Solutions.OAIQ053_KM.KMedian_Analysis_ScalarTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ScalarTransfer

noncomputable def uOne (s : Bool) : ℝ := (2-bit s)*(1+d s)/(2*hh s)
noncomputable def c (p : ℝ) (s : Bool) : ℝ := 1-bit s*p
noncomputable def N (p k : ℝ) (s : Bool) : ℝ := c p s-(1-bit s)*k
noncomputable def ell (p a x : ℝ) (s : Bool) : ℝ := c p s+1-a+bit s*p*x
noncomputable def Q0 (p a k W : ℝ) (s : Bool) : ℝ :=
  N p k s - d s*a + p*W*(hh s*W-2*d s)
noncomputable def Q1 (p a k x : ℝ) (s : Bool) : ℝ :=
  N p k s-(2-bit s)*p*x-d s*(c p s*p-ell p a x s)-hh s*p*(uOne s)^2
noncomputable def Y (p k x : ℝ) (s : Bool) : ℝ :=
  N p k s-p*((2-bit s)*x+(2-bit s)^2/(32/5))

end MetricKMedian.ScalarTransfer


end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Analysis_NormalizedTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ScalarTransfer

noncomputable def stdB (p x w : ℝ) (s : Bool) : ℝ := (2-bit s)*p*(x+w)
noncomputable def stdL (p a x w r : ℝ) (s : Bool) : ℝ :=
  (c p s-(a-1-2*x*p)-stdB p x w s)*r+(2/5)*p*w^2
noncomputable def stdM (p a w r : ℝ) (s : Bool) : ℝ :=
  (1-r)*(a+2*p*w)+c p s*p*r
noncomputable def stdK (p k x w r : ℝ) (s : Bool) : ℝ :=
  N p k s-stdB p x w s*r+(8/5)*p*w^2

end MetricKMedian.ScalarTransfer


end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_Taper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper

variable {I : Type*} [Fintype I]

theorem exists_colocated_inverse {P : ℝ} (hP : 0 < P) (hP1 : P ≤ 1)
    (g : ℝ) (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) :
    ∃ r > 0, mass g P d r=colocatedMass g d := by
  let U := 1+∑ i, (d i)⁻¹
  have hsum : 0 ≤ ∑ i, (d i)⁻¹ := Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (hd i))
  have hU : 0 < U := by dsimp only [U]; linarith only [hsum]
  refine ⟨U, hU, ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : d i=0
  · simp only [hi, marginal_at_zero_distance hP hP1, mul_one, ite_true]
  · have hip : 0 < d i := lt_of_le_of_ne (hd i) (Ne.symm hi)
    have hb : (d i)⁻¹ ≤ ∑ t, (d t)⁻¹ :=
      Finset.single_le_sum (fun t _ => inv_nonneg.mpr (hd t)) (Finset.mem_univ i)
    have hm := mul_le_mul_of_nonneg_right hb hip.le
    rw [inv_mul_cancel₀ hi] at hm
    have hu : 1 ≤ U*d i := by dsimp only [U]; nlinarith only [hm, hip]
    simp only [marginal_zero hu, mul_zero, ite_eq_right hi]

theorem exists_minimal_radius {g P : ℝ} (d : I → ℝ)
    (hg : 0 < g) (hP : 0 < P) (hP1 : P ≤ 1/2) (hd : ∀ i, 0 ≤ d i)
    (htotal : 1 ≤ ∑ _i : I, g) (hcol : colocatedMass g d < 1) :
    ∃ r > 0, mass g P d r=1 ∧ ∀ u, 1 ≤ mass g P d u → u ≤ r := by
  obtain ⟨L, hL, hfull⟩ := exists_full_inverse hP hP1 d hd
  have hmassL : 1 ≤ mass g P d L := by
    simpa only [mass, hfull, mul_one] using htotal
  obtain ⟨U, _hU, hmassU⟩ := exists_colocated_inverse hP (by linarith only [hP1]) g d hd
  have hmassUlt : mass g P d U < 1 := hmassU ▸ hcol
  have hanti := mass_antitone hg.le hP hd
  have hLU : L < U := by
    by_contra hn
    have hh := hanti (le_of_not_gt hn)
    linarith only [hmassL, hmassUlt, hh]
  have hcont : Continuous (mass g P d) := continuous_mass
  have hex : ∃ r ∈ Set.Icc L U, mass g P d r=1 :=
    intermediate_value_Icc' hLU.le hcont.continuousOn ⟨hmassUlt.le, hmassL⟩
  let S := Set.Icc L U ∩ (mass g P d) ⁻¹' {1}
  have hcompact : IsCompact S := isCompact_Icc.inter_right
    (isClosed_singleton.preimage hcont)
  have hne : S.Nonempty := by
    obtain ⟨r, hr, heq⟩ := hex
    exact ⟨r, hr, heq⟩
  obtain ⟨r, hr, hmax⟩ := hcompact.exists_isMaxOn hne continuous_id.continuousOn
  refine ⟨r, hL.trans_le hr.1.1, hr.2, ?_⟩
  intro u hu
  by_contra hn
  have hru : r < u := lt_of_not_ge hn
  have hupper : u ≤ U := by
    by_contra hnu
    have hh := hanti (le_of_lt (lt_of_not_ge hnu))
    linarith only [hu, hmassUlt, hh]
  have heq : mass g P d u=1 := le_antisymm ((hanti hru.le).trans_eq hr.2) hu
  have hus : u ∈ S := ⟨⟨hr.1.1.trans hru.le, hupper⟩, heq⟩
  have hh := hmax hus
  exact (not_le_of_gt hru) hh

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliPolynomial
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

def polynomial {m : ℕ} (S : Fin m → Finset (Fin n)) (c : Fin m → ℚ)
    (q : Fin n → Bool) : ℚ := ∑ j, c j*∏ i ∈ S j, flag q i

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalTaperAffine
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset

theorem marginal_affine {P d t : ℚ} {x : ℝ} (hP : 0 < (P:ℝ))
    (ha : (x*(d:ℝ) ≤ 1-(P:ℝ) ↔ t*d ≤ 1-P))
    (hb : (1 ≤ x*(d:ℝ) ↔ 1 ≤ t*d)) :
    marginal P d x=(aCoef P d t:ℝ)-x*(bCoef P d t:ℝ) := by
  rw [marginal_piecewise hP]
  by_cases hs : t*d ≤ 1-P
  · rw [ite_eq_left (ha.mpr hs)]
    simp only [aCoef,bCoef,ite_eq_left hs,Rat.cast_one,Rat.cast_zero,mul_zero,sub_zero]
  · rw [ite_eq_right (fun he => hs (ha.mp he))]
    by_cases hz : 1 ≤ t*d
    · rw [ite_eq_left (hb.mpr hz)]
      simp only [aCoef,bCoef,ite_eq_right hs,ite_eq_left hz,Rat.cast_zero,mul_zero,sub_zero]
    · rw [ite_eq_right (fun he => hz (hb.mp he))]
      simp only [aCoef,bCoef,ite_eq_right hs,ite_eq_right hz,Rat.cast_div,Rat.cast_one]
      ring

variable {I : Type*} [Fintype I]

theorem cuts_in_interval {P : ℚ} {d : I → ℚ} (hd : ∀ i, 0 ≤ d i) (hP : P < 1)
    (a b t : ℚ) (hgap : ∀ q ∈ breakpoints P d, q ≤ a ∨ b ≤ q)
    (ht : a < t ∧ t < b) (x : ℝ) (hx : (a:ℝ) < x ∧ x < (b:ℝ)) :
    (∀ i, (x*(d i:ℝ) ≤ 1-(P:ℝ) ↔ t*d i ≤ 1-P)) ∧
    (∀ i, (1 ≤ x*(d i:ℝ) ↔ 1 ≤ t*d i)) := by
  have ht' : (a:ℝ) < (t:ℝ) ∧ (t:ℝ) < (b:ℝ) := by exact_mod_cast ht
  have hh := same_interval_cuts (breakpoints P d) a b hgap x t hx ht'
  have hcuts : ∀ i, (x*(d i:ℝ) ≤ 1-(P:ℝ) ↔ t*d i ≤ 1-P) ∧
      (1 ≤ x*(d i:ℝ) ↔ 1 ≤ t*d i) := by
    intro i
    by_cases hz : d i=0
    · simp only [hz,Rat.cast_zero,mul_zero]
      constructor
      · have hp : (0:ℝ) ≤ 1-(P:ℝ) := by exact_mod_cast (sub_nonneg.mpr hP.le)
        exact iff_of_true hp (sub_nonneg.mpr hP.le)
      · norm_num
    · have hdi : 0 < d i := lt_of_le_of_ne (hd i) (Ne.symm hz)
      have hdR : (0:ℝ) < d i := by exact_mod_cast hdi
      have hcut1 : (1-P)/d i ∈ breakpoints P d := by
        exact mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ (mem_image_of_mem _ (mem_univ i))))
      have hcut2 : 1/d i ∈ breakpoints P d := by
        exact mem_insert_of_mem (mem_insert_of_mem (mem_union_right _ (mem_image_of_mem _ (mem_univ i))))
      have h1 := (hh _ hcut1).1
      have h2 := (hh _ hcut2).2
      simp only [Rat.cast_div,Rat.cast_sub,Rat.cast_one] at h1 h2
      rw [le_div_iff₀ hdR,le_div_iff₀ hdR] at h1
      rw [div_le_iff₀ hdR,div_le_iff₀ hdR] at h2
      constructor
      · exact h1.trans (by norm_cast)
      · exact h2.trans (by norm_cast)
  exact ⟨fun i => (hcuts i).1,fun i => (hcuts i).2⟩

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalTaperCandidates
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

theorem mass_upper (g P : ℚ) (d : I → ℚ) (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1)
    (hd : ∀ i, 0 ≤ d i) :
    mass g P (fun i => (d i:ℝ)) (upper d)=colocatedMass g (fun i => (d i:ℝ)) := by
  apply sum_congr rfl
  intro i _
  by_cases hi : d i=0
  · simp only [hi,Rat.cast_zero,marginal_at_zero_distance hP hP1,mul_one,ite_true]
  · have hip : 0 < d i := lt_of_le_of_ne (hd i) (Ne.symm hi)
    have hb : (d i)⁻¹ ≤ ∑ t, (d t)⁻¹ := single_le_sum
      (fun t _ => inv_nonneg.mpr (hd t)) (mem_univ i)
    have hm := mul_le_mul_of_nonneg_right hb hip.le
    rw [inv_mul_cancel₀ hi] at hm
    have hu : 1 ≤ upper d*d i := by dsimp only [upper]; nlinarith only [hm,hip]
    have hur : 1 ≤ (upper d:ℝ)*(d i:ℝ) := by exact_mod_cast hu
    have hir : (d i:ℝ) ≠ 0 := by exact_mod_cast hi
    simp only [marginal_zero hur,mul_zero,ite_eq_right hir]

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalTaper
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

theorem cast_rationalMarginal (P d r : ℚ) :
    (rationalMarginal P d r:ℝ)=marginal P d r := by
  simp only [rationalMarginal,marginal,Rat.cast_min,Rat.cast_max,
    Rat.cast_div,Rat.cast_sub,Rat.cast_mul,Rat.cast_one,Rat.cast_zero]

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalTaperZero
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
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

omit [Fintype I] in
theorem extend_spec (own Z : Finset I) (Δ : ℕ) (hsub : own ⊆ Z)
    (hown : own.card ≤ Δ) (hZ : Δ ≤ Z.card) :
    own ⊆ extend own Z Δ ∧ extend own Z Δ ⊆ Z ∧ (extend own Z Δ).card=Δ := by
  let L := (((Z \ own).sort (· ≤ ·)).take (Δ-own.card)).toFinset
  have hL : L ⊆ Z \ own := by
    intro i hi
    exact (mem_sort (· ≤ ·)).mp (List.mem_of_mem_take (List.mem_toFinset.mp hi))
  have hdis : Disjoint own L := by
    apply disjoint_left.mpr
    intro i hi hli
    exact (mem_sdiff.mp (hL hli)).2 hi
  refine ⟨subset_union_left,union_subset hsub (hL.trans sdiff_subset),?_⟩
  change (own ∪ L).card=Δ
  rw [card_union_of_disjoint hdis]
  have hc : L.card=Δ-own.card := by
    rw [List.toFinset_card_of_nodup ((sort_nodup (Z \ own) (· ≤ ·)).take),List.length_take,
      length_sort,card_sdiff_of_subset hsub,min_eq_left (Nat.sub_le_sub_right hZ _)]
  rw [hc,Nat.add_sub_of_le hown]

theorem zero_data (g : ℚ) (d : I → ℚ) (own : Finset I) (Δ : ℕ)
    (_hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hcol : 1 ≤ colocatedMass g (fun i => (d i:ℝ)))
    (hown : ∀ i ∈ own, d i=0) (howncard : own.card ≤ Δ) :
    let q := zeroMarginal d own Δ
    (∀ i, 0 ≤ q i) ∧ (∀ i, q i ≤ 1) ∧ (∑ i, g*q i=1) ∧
      (∑ i, q i=Δ) ∧ (∀ i ∈ own, q i=1) ∧ (∀ i, 0 < q i → d i=0) := by
  let Z := zeroSources d
  have hz : (Z.card:ℝ)*(g:ℝ)=colocatedMass g (fun i => (d i:ℝ)) := by
    simp only [Z,zeroSources,colocatedMass,← sum_filter,sum_const,nsmul_eq_mul,
      Rat.cast_eq_zero]
  have hzcard : Δ ≤ Z.card := by
    have hh : (Δ:ℝ) ≤ Z.card := by nlinarith only [hcol,hz,hunit]
    exact_mod_cast hh
  have hsub : own ⊆ Z := by intro i hi; exact mem_filter.mpr ⟨mem_univ _,hown i hi⟩
  obtain ⟨hownS,hSZ,hcard⟩ := extend_spec own Z Δ hsub howncard hzcard
  change (∀ i, 0 ≤ zeroMarginal d own Δ i) ∧ _
  have hsum : (∑ i, zeroMarginal d own Δ i)=(Δ:ℚ) := by
    simp only [zeroMarginal,← sum_filter,filter_univ_mem,sum_const,nsmul_eq_mul,mul_one]
    exact_mod_cast hcard
  refine ⟨?_,?_,?_,hsum,?_,?_⟩
  · intro i; unfold zeroMarginal; split_ifs <;> norm_num
  · intro i; unfold zeroMarginal; split_ifs <;> norm_num
  · rw [← mul_sum,hsum]; exact_mod_cast hunit
  · intro i hi; exact ite_eq_left (hownS hi)
  · intro i hi
    have hm : i ∈ zeroSelection d own Δ := by
      by_contra hn
      simp only [zeroMarginal,ite_eq_right hn] at hi
      exact lt_irrefl _ hi
    exact (mem_filter.mp (hSZ hm)).2

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalTaperData
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

omit [LinearOrder I] in
theorem cast_rationalColocatedMass (g : ℚ) (d : I → ℚ) :
    (rationalColocatedMass g d:ℝ)=colocatedMass g (fun i => (d i:ℝ)) := by
  simp only [rationalColocatedMass,colocatedMass,Rat.cast_sum,apply_ite,
    Rat.cast_zero,Rat.cast_eq_zero]

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_DeletionGeometry
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}
local instance deletionGeometryPseudoMetricSpace : PseudoMetricSpace (Fin I.n) := I.pseudoMetric

structure Serving (U : Finset (Fin I.n)) where
  assignment : ↥I.clients → ↥U
  assignment_cost : ∀ j, dist j.val (assignment j).val=nearest I j U
  other : ↥U → ↥U
  other_ne : ∀ t, other t ≠ t
  other_nearest : ∀ t u, u ≠ t → dist t.val (other t).val ≤ dist t.val u.val

namespace Serving
variable {U : Finset (Fin I.n)}

def radius (D : Serving (I:=I) U) (t : ↥U) : ℝ := dist t.val (D.other t).val

noncomputable def group (D : Serving (I:=I) U) (t : ↥U) : Finset ↥I.clients :=
  univ.filter (fun j => D.assignment j=t)

noncomputable def groupCost (D : Serving (I:=I) U) (t : ↥U) : ℝ :=
  ∑ j ∈ D.group t, nearest I j U

end Serving
end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalPhysicalGraphInstance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}
local instance instLinearOrderCopy_1 : LinearOrder (CopyState.Copy (F := F) Δ) := copyOrder

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseCountStatistic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseBernoulli
open Finset
variable {n : ℕ}

@[simp] theorem cast_flag (q : Fin n → Bool) (i : Fin n) :
    (flag q i:ℝ)=CountStatistic.bit q i := by
  cases he : q i <;> simp [flag,CountStatistic.bit,he]

end MetricKMedian.SparseBernoulli
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalPhysicalCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}
local instance rationalPhysicalCountCopyOrder : LinearOrder (CopyState.Copy (F := F) Δ) := copyOrder

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseGridRounding
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
attribute [-simp] _root_.OAI.MetricKMedian.SparseTargetSubset.point_initial
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

theorem base_sum_le (q : Fin n → ℚ) (hq : ∀ i, 0 ≤ q i) (K : ℕ)
    (hs : (∑ i, q i)=(K:ℚ)) : (∑ i, base q i) ≤ K := by
  have hh : (∑ i, (base q i:ℚ)) ≤ (K:ℚ) :=
    (sum_le_sum (fun i _ => Nat.floor_le (hq i))).trans_eq hs
  exact_mod_cast hh

theorem fraction_sum (q : Fin n → ℚ) (hq : ∀ i, 0 ≤ q i) (K : ℕ)
    (hs : (∑ i, q i)=(K:ℚ)) :
    (∑ i, point (fraction q) i)=(K-∑ i,base q i:ℕ) := by
  simp only [fraction,point,Vector.getElem_ofFn,sum_sub_distrib,hs,
    Nat.cast_sub (base_sum_le q hq K hs),Nat.cast_sum]

theorem count_cast (q : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, point p i=0 ∨ point p i=1) (i : Fin n) :
    (count q p i:ℚ)=(base q i:ℚ)+point p i := by
  rcases hp i with hi | hi <;> simp [count,hi]

end MetricKMedian.SparseGridRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseRescaledInner
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
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

theorem piece_cap (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ) (p : Fin t → ℚ)
    (K : Fin t → ℕ) (Δ : ℕ) (hy : ∀ i,0 ≤ y i) (hp : ∀ j,0 < p j)
    (hm : ∀ j,∑ i∈P j,y i=p j) (hK : ∀ j,K j ≤ Δ) :
    ∀ i j,piece P y p K i j ≤ Δ := by
  intro i j
  by_cases hi : i∈P j
  · have hyP : y i ≤ p j := (single_le_sum (fun i _ => hy i) hi).trans_eq (hm j)
    have he : piece P y p K i j ≤ (K j:ℚ) := by
      simp only [piece,ite_eq_left hi]
      apply (div_le_iff₀ (hp j)).mpr
      exact mul_le_mul_of_nonneg_left hyP (Nat.cast_nonneg _)
    exact he.trans (Nat.cast_le.mpr (hK j))
  · simp only [piece,ite_eq_right hi]
    exact Nat.cast_nonneg _

theorem piece_sum (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ) (p : Fin t → ℚ)
    (K : Fin t → ℕ) (hp : ∀ j,0 < p j) (hm : ∀ j,∑ i∈P j,y i=p j) :
    ∀ j,(∑ i,piece P y p K i j)=(K j:ℚ) := by
  intro j
  simp only [piece,sum_ite_mem,univ_inter,← sum_div,← mul_sum,hm]
  exact mul_div_cancel_right₀ _ (hp j).ne'

end MetricKMedian.SparseRescaledInner
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBundleEncoding
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseBundleEncoding
open Finset
variable {n m : ℕ}

def encode (q : Fin n → Fin m → ℚ) (G : SparseCounts.Table n m) :
    Fin m → Finset (Fin n) :=
  fun j => univ.filter (fun i => G j i = SparseGridRounding.base (fun i => q i j) i + 1)

def decode (q : Fin n → Fin m → ℚ) (ξ : Fin m → Finset (Fin n)) :
    SparseCounts.Table n m :=
  fun j i => SparseGridRounding.base (fun i => q i j) i + if i ∈ ξ j then 1 else 0

theorem decode_encode (q : Fin n → Fin m → ℚ) (G : SparseCounts.Table n m)
    (hG : ∀ j i, G j i = SparseGridRounding.base (fun i => q i j) i ∨
      G j i = SparseGridRounding.base (fun i => q i j) i + 1) :
    decode q (encode q G) = G := by
  funext j i
  rcases hG j i with h | h <;> simp [decode, encode, h]

end MetricKMedian.SparseBundleEncoding

namespace MetricKMedian.SparseRescaledInner
open Finset
variable {n t : ℕ}

def encodedCount (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ)
    (p : Fin t → ℚ) (K : Fin t → ℕ) (ξ : Fin t → Finset (Fin n)) (a : Fin t × Fin n) : ℕ :=
  SparseBundleEncoding.decode (piece P y p K) ξ a.1 a.2

theorem cast_scaled_piece (P : Fin t → Finset (Fin n)) (y : Fin n → ℚ)
    (p : Fin t → ℚ) (K : Fin t → ℕ) (g : ℝ) (i : Fin n) (j : Fin t) :
    g * (piece P y p K i j : ℝ) =
      if i ∈ P j then (g * (K j : ℝ)) * (y i : ℝ) / (p j : ℝ) else 0 := by
  simp only [piece, apply_ite, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_zero]
  split_ifs <;> ring

end MetricKMedian.SparseRescaledInner
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparsePreparedLaw
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw
open SparseSignedPreparation (State)
variable {n m f : ℕ}

theorem total_le (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) (j : Fin n) : total D q Δ z j ≤ Δ := Nat.sub_le _ _

theorem total_half (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) (j : Fin n) {g : ℝ} (hg : 0 < g) (heven : Even Δ)
    (hunit : g*(Δ:ℝ)=1) : (1/2:ℝ) ≤ g*(total D q Δ z j:ℝ) :=
  (Preparation.grid_clip hg heven hunit (∑ e,activationCount D q z e j)).2.2.1

end MetricKMedian.SparsePrepared
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparsePreparedBudget
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
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

theorem activation_sum (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ)
    (z : State n m) (e : Fin m) :
    (∑ j,activationCount D q z e j)=(D e).card*base q e+(z.2.1 e).card := by
  simp only [activationCount,sum_add_distrib,sum_ite_mem,univ_inter,sum_const,
    nsmul_eq_mul,mul_one,Nat.cast_id]

def discarded (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) (j : Fin n) : ℚ :=
  ((∑ e,activationCount D q z e j):ℕ)-
    (min (∑ e,activationCount D q z e j) (Δ/2):ℕ)

end MetricKMedian.SparsePrepared
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_SupplierMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation.SupplierStars
open Finset
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

def supplier (next : T → T) : Star I T → I ⊕ T
  | .inl i => .inl i
  | .inr (.inl st) => .inr st.2
  | .inr (.inr t) => .inr (next t)

end MetricKMedian.Preparation.SupplierStars
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_SupplierCharges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation.SupplierStars
open Finset
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

noncomputable def connectionCharge (P A : T → Finset I) (y d : I → ℝ)
    (L : T → ℝ) (κ β δ : ℝ) : Star I T → ℝ
  | .inl i => d i
  | .inr (.inl st) => κ*((∑ i ∈ A st.1 ∩ P st.2, y i*d i)/(∑ i ∈ A st.1 ∩ P st.2, y i))
  | .inr (.inr t) => (β+1+δ)*L t

end MetricKMedian.Preparation.SupplierStars
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}
local instance sparseDeletionPseudoMetricSpace : PseudoMetricSpace (Fin I.n) := I.pseudoMetric

noncomputable def denseBall (O : Finset (Fin I.n)) (i : Fin I.n) : Finset (Fin I.n) :=
  I.clients.filter (fun j => dist j i < nearest I i O/3)

def Sparse (F O : Finset (Fin I.n)) (ρ : ℝ) : Prop :=
  ∀ i ∈ F, nearest I i O*(denseBall (I:=I) O i).card ≤ ρ*cost I O

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_Sparsification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}
local instance sparsificationPseudoMetricSpace : PseudoMetricSpace (Fin I.n) := I.pseudoMetric

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_SparsifyEnumeration
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def witnessedRestriction (I : Instance) (F : Finset (Fin I.n))
    (P : Finset (Fin I.n × Fin I.n)) : Finset (Fin I.n) :=
  F.filter (fun i => ∀ p ∈ P, I.distance p.1 p.2 ≤ I.distance p.1 i)

def sparseBranches (I : Instance) (F : Finset (Fin I.n)) (b : ℕ) : Finset (Finset (Fin I.n)) :=
  (deletionChoices (F ×ˢ F) b).image (witnessedRestriction I F)

variable {I : Instance}
local instance sparsifyEnumerationPseudoMetricSpace : PseudoMetricSpace (Fin I.n) := I.pseudoMetric

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_CompletionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable (I : Instance)
local instance completionGeometryPseudoMetricSpace : PseudoMetricSpace (Fin I.n) := I.pseudoMetric

structure CloseCenters (G : Finset (Fin I.n)) (O : Finset (Fin I.n)) (δ : ℝ) where
  radius : ↥G → ℝ
  radius_nonneg : ∀ t, 0 ≤ radius t
  separated : ∀ t u, t ≠ u → radius t ≤ dist t.val u.val
  matchTo : ↥G → Fin I.n
  match_mem : ∀ t, matchTo t ∈ O
  close : ∀ t, dist t.val (matchTo t) < δ*radius t

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_LocalCompletion
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}
local instance localCompletionPseudoMetricSpace : PseudoMetricSpace (Fin I.n) := I.pseudoMetric

namespace CloseCenters
variable {G O : Finset (Fin I.n)} {δ : ℝ}

noncomputable def region (C : CloseCenters I G O δ) (t : ↥G) : Finset (Fin I.n) :=
  I.clients.filter (fun j => dist j t.val ≤ C.radius t/3)

noncomputable def matched (C : CloseCenters I G O δ) : Finset (Fin I.n) :=
  univ.image C.matchTo

noncomputable def backup (C : CloseCenters I G O δ) : Finset (Fin I.n) :=
  O \ C.matched

end CloseCenters
end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_CloseFromServing
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}
local instance closeFromServingPseudoMetric : PseudoMetricSpace (Fin I.n) := I.pseudoMetric

namespace Serving
variable {U O : Finset (Fin I.n)} {δ : ℝ}

noncomputable def bad (D : Serving (I:=I) U) (O : Finset (Fin I.n)) (δ : ℝ) : Finset ↥U :=
  univ.filter (fun t => δ*D.radius t ≤ nearest I t O)

noncomputable def good (D : Serving (I:=I) U) (O : Finset (Fin I.n)) (δ : ℝ) : Finset (Fin I.n) :=
  (univ \ D.bad O δ).image Subtype.val

theorem good_sub (D : Serving (I:=I) U) : D.good O δ ⊆ U := by
  intro i hi
  obtain ⟨t,_,rfl⟩ := mem_image.mp hi
  exact t.property

end Serving
end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_CompletionSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}
local instance instPseudoMetricSpaceFinN : PseudoMetricSpace (Fin I.n) := I.pseudoMetric

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_RationalLocalChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def rationalRegion (I : Instance) (r : Fin I.n → ℚ) (t : Fin I.n) : Finset (Fin I.n) :=
  I.clients.filter (fun j => 3*I.distance j t ≤ r t)

def rationalCandidates (I : Instance) (F : Finset (Fin I.n)) (r : Fin I.n → ℚ)
    (δ : ℚ) (t : Fin I.n) : Finset (Fin I.n) :=
  F.filter (fun a => I.distance t a ≤ δ*r t)

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_RationalCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}
local instance instPseudoMetricSpaceFinN_1 : PseudoMetricSpace (Fin I.n) := I.pseudoMetric

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_CompletionEnumeration
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}

namespace Serving
variable {U O : Finset (Fin I.n)} {δ : ℝ}

local instance completionEnumerationPseudoMetric_rfd671d_1 : PseudoMetricSpace (Fin I.n) := I.pseudoMetric
noncomputable def badSet (D : Serving (I:=I) U) (O : Finset (Fin I.n)) (δ : ℝ) :
    Finset (Fin I.n) := (D.bad O δ).image Subtype.val

end Serving

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Analysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian

def unitCoverage : Coverage.Input where
  m := 1
  n := 1
  incident _ _ := true
  k := 1
  m_pos := Nat.zero_lt_one
  k_pos := le_rfl
  k_le := le_rfl

end MetricKMedian

end Inline_PCPInherited

end OAI
end


