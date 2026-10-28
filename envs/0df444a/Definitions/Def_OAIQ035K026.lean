-- Prove2me | Definitions.Def_OAIQ035K026
-- name    : OAIQ035K026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:57:56.544916+00:00
-- url     : https://prove2.me/theorems/f9814fbc-0497-4e09-ae3a-d02af40e5fd0
-- title:
--   Definitions bundle OAIQ035K026 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 36 declarations of OpenAI's Lean: 19 definitions, 1 inductive type or structure and 16 theorems. The definitions and types are `OAI.MetricKMedian.Reduction.Serving`, `OAI.MetricKMedian.Reduction.Serving.bad`, `OAI.MetricKMedian.Reduction.Serving.badSet`, `OAI.MetricKMedian.Reduction.Serving.good`, `OAI.MetricKMedian.Reduction.Serving.group`, `OAI.MetricKMedian.Reduction.Serving.groupCost`, `OAI.MetricKMedian.Reduction.Serving.radius`, `OAI.MetricKMedian.Reduction.Sparse`, `OAI.MetricKMedian.Reduction.closeFromServingPseudoMetric`, `OAI.MetricKMedian.Reduction.deletionGeometryPseudoMetricSpace`, `OAI.MetricKMedian.Reduction.denseBall`, `OAI.MetricKMedian.Reduction.instPseudoMetricSpaceFinN`, `OAI.MetricKMedian.Reduction.instPseudoMetricSpaceFinN_1`, `OAI.MetricKMedian.Reduction.sparseDeletionPseudoMetricSpace`, `OAI.MetricKMedian.Reduction.sparsificationPseudoMetricSpace`, `OAI.MetricKMedian.Reduction.sparsifyEnumerationPseudoMetricSpace`, `OAI.MetricKMedian.ScalarTransfer.stdB`, `OAI.MetricKMedian.ScalarTransfer.uOne`, `OAI.MetricKMedian.SparseBernoulli.polynomial`, `OAI.MetricKMedian.SparseBernoulli.reference`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Analysis_NormalizedTransfer`, `KMedian_Analysis_ScalarTransfer`, `KMedian_Probability_BernoulliPolynomial`, `KMedian_Probability_BernoulliRealTransfer`, `KMedian_Process_Taper`, `KMedian_Reduction_CloseFromServing`, `KMedian_Reduction_CompletionEnumeration`, `KMedian_Reduction_CompletionSelection`, `KMedian_Reduction_DeletionGeometry`, `KMedian_Reduction_RationalCompletion`, `KMedian_Reduction_Sparsification`, `KMedian_Reduction_SparsifyEnumeration`, `KMedian_Rounding_RationalTaper`, `KMedian_Rounding_RationalTaperAffine`, `KMedian_Rounding_RationalTaperCandidates`, `KMedian_Rounding_RationalTaperData`, `KMedian_Rounding_RationalTaperZero`, `KMedian_Sparse_SparseCountStatistic`, `KMedian_Sparse_SparseDeletion`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K001`, `OAIQ035K002`, `OAIQ035K004`, `OAIQ035K005`, `OAIQ035K006`, `OAIQ035K008` and `OAIQ035K011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K036` and `OAIQ035K037`; the statements `OAI.MetricKMedian.Reduction.CloseCenters.complete_of_choices`, `OAI.MetricKMedian.Reduction.Serving.bad_count`, `OAI.MetricKMedian.SparseBernoulli.count_mean` and `OAI.MetricKMedian.SparseBernoulli.quadratic_variance`; the proofs of `OAI.MetricKMedian.Reduction.CloseCenters.complete_of_choices`, `OAI.MetricKMedian.Reduction.Serving.bad_count`, `OAI.MetricKMedian.SparseBernoulli.count_failure`, `OAI.MetricKMedian.SparseBernoulli.count_mean` and `OAI.MetricKMedian.SparseBernoulli.quadratic_variance`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K001
import Definitions.Def_OAIQ035K002
import Definitions.Def_OAIQ035K004
import Definitions.Def_OAIQ035K005
import Definitions.Def_OAIQ035K006
import Definitions.Def_OAIQ035K008
import Definitions.Def_OAIQ035K011

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_ScalarTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ScalarTransfer

noncomputable def uOne (s : Bool) : ℝ := (2-bit s)*(1+d s)/(2*hh s)

end MetricKMedian.ScalarTransfer


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_NormalizedTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ScalarTransfer

noncomputable def stdB (p x w : ℝ) (s : Bool) : ℝ := (2-bit s)*p*(x+w)

end MetricKMedian.ScalarTransfer


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliPolynomial
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
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliRealTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n : ℕ}

noncomputable def reference (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    FiniteLaw (Fin n → Bool) :=
  FiniteLaw.bernoulli (fun i => (p i:ℝ))
    (fun i => by exact_mod_cast (hp i).1) (fun i => by exact_mod_cast (hp i).2)

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_Taper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper

theorem marginal_antitone {P d : ℝ} (hP : 0 < P) (hd : 0 ≤ d) : Antitone (marginal P d) := by
  intro r s hrs
  apply min_le_min_left
  apply div_le_div_of_nonneg_right _ hP.le
  apply max_le_max_right
  nlinarith only [mul_le_mul_of_nonneg_right hrs hd]

theorem lower_comparison {P d r : ℝ} (hP : 0 < P) (h : marginal P d r < 1) :
    1-P*marginal P d r ≤ r*d := by
  have hright : max (1-r*d) 0/P < 1 := by
    by_contra hn
    have heq : marginal P d r=1 := min_eq_left (le_of_not_gt hn)
    rw [heq] at h
    exact lt_irrefl _ h
  have heq : marginal P d r=max (1-r*d) 0/P := min_eq_right hright.le
  rw [heq, mul_div_cancel₀ _ (ne_of_gt hP)]
  have hh := le_max_left (1-r*d) 0
  linarith only [hh]

theorem upper_comparison {P d r : ℝ} (hP : 0 < P) (h : 0 < marginal P d r) :
    r*d ≤ 1-P*marginal P d r := by
  have hrd : r*d < 1 := by
    by_contra hn
    rw [marginal_zero (le_of_not_gt hn)] at h
    exact lt_irrefl _ h
  have hh : marginal P d r ≤ (1-r*d)/P := by
    unfold marginal
    rw [max_eq_left (by linarith only [hrd])]
    exact min_le_right _ _
  have hb := (le_div_iff₀ hP).mp hh
  nlinarith only [hb]

variable {I : Type*} [Fintype I]

theorem mass_antitone {g P : ℝ} {d : I → ℝ} (hg : 0 ≤ g) (hP : 0 < P)
    (hd : ∀ i, 0 ≤ d i) : Antitone (mass g P d) := by
  intro r s hrs
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (marginal_antitone hP (hd i) hrs) hg)

theorem exists_full_inverse {P : ℝ} (hP : 0 < P) (hP1 : P ≤ 1/2)
    (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) :
    ∃ r > 0, ∀ i, marginal P (d i) r=1 := by
  let D := ∑ i, d i
  have hD : 0 ≤ D := Finset.sum_nonneg (fun i _ => hd i)
  have hden : 0 < 2*(1+D) := by linarith only [hD]
  refine ⟨1/(2*(1+D)), one_div_pos.mpr hden, ?_⟩
  intro i
  apply marginal_one hP
  have hi : d i ≤ D := Finset.single_le_sum (fun t _ => hd t) (Finset.mem_univ i)
  have hh : (1/(2*(1+D)))*d i ≤ 1/2 := by
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ hden).mpr
    linarith only [hi]
  linarith only [hh, hP1]

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
-- module Solutions.OAIQ035_KM.KMedian_Reduction_DeletionGeometry
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
-- module Solutions.OAIQ035_KM.KMedian_Reduction_CloseFromServing
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseDeletion
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
-- module Solutions.OAIQ035_KM.KMedian_Reduction_CompletionSelection
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
-- module Solutions.OAIQ035_KM.KMedian_Reduction_RationalCompletion
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
-- module Solutions.OAIQ035_KM.KMedian_Reduction_CompletionEnumeration
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

noncomputable def badSet (D : Serving (I:=I) U) (O : Finset (Fin I.n)) (δ : ℝ) :
    Finset (Fin I.n) := (D.bad O δ).image Subtype.val

end Serving

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_Sparsification
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
-- module Solutions.OAIQ035_KM.KMedian_Reduction_SparsifyEnumeration
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
local instance sparsifyEnumerationPseudoMetricSpace : PseudoMetricSpace (Fin I.n) := I.pseudoMetric

end MetricKMedian.Reduction
end
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

theorem marginal_piecewise {P d r : ℝ} (hP : 0 < P) :
    marginal P d r=if r*d ≤ 1-P then 1 else
      if 1 ≤ r*d then 0 else (1-r*d)/P := by
  split_ifs with hs hz
  · exact marginal_one hP hs
  · exact marginal_zero hz
  · have hp : 0 ≤ 1-r*d := by linarith
    have hh : (1-r*d)/P ≤ 1 := (div_le_one₀ hP).mpr (by linarith)
    exact (congrArg (min 1) (congrArg (fun a => a/P) (max_eq_left hp))).trans (min_eq_right hh)

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
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalTaperZero
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseCountStatistic
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


