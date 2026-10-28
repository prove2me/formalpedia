-- Prove2me | Definitions.Def_OAIQ035K011
-- name    : OAIQ035K011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:54:02.377386+00:00
-- url     : https://prove2.me/theorems/b56c3f75-b3f0-4ae4-9bff-87749c327928
-- title:
--   Definitions bundle OAIQ035K011 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 59 declarations of OpenAI's Lean: 37 definitions, 5 inductive types or structures and 17 theorems. The definitions and types are `OAI.MetricKMedian.PhysicalBatchLaw.unbalanced`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.Cut`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.Input`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.Program.State`, `OAI.MetricKMedian.Preparation.parameterEnvelope`, `OAI.MetricKMedian.Preparation.parameterEnvelopeFar`, `OAI.MetricKMedian.Preparation.parameterEnvelopeNear`, `OAI.MetricKMedian.Preparation.relevantRadius`, `OAI.MetricKMedian.Preparation.supplierBundle`, `OAI.MetricKMedian.Preparation.supplierOutside`, `OAI.MetricKMedian.Preparation.upperBit`, `OAI.MetricKMedian.RationalRetain.keep`, `OAI.MetricKMedian.Reduction.Enumeration.pairs`, `OAI.MetricKMedian.Reduction.Enumeration.words`, `OAI.MetricKMedian.Reduction.deletionChoices`, `OAI.MetricKMedian.Reduction.pickSingleton`, `OAI.MetricKMedian.ScalarTransfer.T1`, `OAI.MetricKMedian.ScalarTransfer.T2`, `OAI.MetricKMedian.ScalarTransfer.Yprime`, `OAI.MetricKMedian.ScalarTransfer.d`, `OAI.MetricKMedian.ScalarTransfer.hh`, `OAI.MetricKMedian.ScalarTransfer.uZero`, `OAI.MetricKMedian.SourceBalance.amount`, `OAI.MetricKMedian.SourceBalance.bias`, `OAI.MetricKMedian.SourceBalance.negative`, `OAI.MetricKMedian.SourceBalance.nonzero`, `OAI.MetricKMedian.SparseBernoulli.countCoefficients`, `OAI.MetricKMedian.SparseBernoulli.countSets`, `OAI.MetricKMedian.SparseBernoulli.pairCoefficient`, `OAI.MetricKMedian.SparseBernoulli.pairSet`, `OAI.MetricKMedian.SparseCounts.target`, `OAI.MetricKMedian.SparseGraph.target`, `OAI.MetricKMedian.SparseOuterLaw.Program.Input`, `OAI.MetricKMedian.SparseOuterLaw.targetMean`, `OAI.MetricKMedian.SparseStarActivation.Program.dummy`, `OAI.MetricKMedian.SparseStarActivation.upper`, `OAI.MetricKMedian.SparseTargetSubset.Program.Input`, `OAI.MetricKMedian.Taper.GraphData`, `OAI.MetricKMedian.Taper.GraphData.Good`, `OAI.MetricKMedian.Taper.colocatedMass` and 2 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Analysis_ScalarTransfer`, `KMedian_Geometry_RationalBrackets`, `KMedian_Preparation_NearestAssignmentGeometry`, `KMedian_Preparation_PreparationParameters`, `KMedian_Preparation_PreparationStars`, `KMedian_Preparation_RepresentativeProgram`, `KMedian_Preparation_SupplierAllocation`, `KMedian_Probability_BernoulliSquare`, `KMedian_Process_CountSource`, `KMedian_Process_PhysicalBatchLaw`, `KMedian_Process_SourceBalance`, `KMedian_Process_Taper`, `KMedian_Process_TaperGraph`, `KMedian_Programs_BoundedEnumerationProgram`, `KMedian_Programs_OuterLawProgram`, `KMedian_Programs_RestrictionProgram`, `KMedian_Programs_StarActivationProgram`, `KMedian_Reduction_RationalLocalChoice`, `KMedian_Reduction_RationalThreshold`, `KMedian_Rounding_ExceptionalStar`, `KMedian_Rounding_GridClipping`, `KMedian_Rounding_RationalRetain`, `KMedian_Rounding_TargetSubsetProgram`, `KMedian_Sparse_SparseCountRun`, `KMedian_Sparse_SparseCountStatistic`, `KMedian_Sparse_SparseGraphRun`, `KMedian_Sparse_SparseOuterMoments`, `KMedian_Sparse_SparseStarActivation`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K024`, `OAIQ035K025`, `OAIQ035K026` and `OAIQ035K044`; the statements `OAI.MetricKMedian.Certificates.T1_actual_pos`, `OAI.MetricKMedian.Certificates.T2_actual_pos`, `OAI.MetricKMedian.Certificates.Yprime_actual_bounds`, `OAI.MetricKMedian.CopyState.round_backup`, `OAI.MetricKMedian.CopyState.unbalanced_count_change`, `OAI.MetricKMedian.CopyState.unbalanced_small_change`, `OAI.MetricKMedian.FixedBatch.masked_biased_linear_bound`, `OAI.MetricKMedian.FixedBatch.masked_mass_sum`, `OAI.MetricKMedian.FixedBatch.masked_total_bound`, `OAI.MetricKMedian.RationalPhysicalKernel.graph_data`, `OAI.MetricKMedian.RationalPhysicalKernel.graph_data_all`, `OAI.MetricKMedian.SparseCopyState.physical_count_tail` and `OAI.MetricKMedian.Taper.GraphData.drift`; the proofs of `OAI.MetricKMedian.Certificates.T1_actual_pos`, `OAI.MetricKMedian.Certificates.T2_actual_pos`, `OAI.MetricKMedian.Certificates.Yprime_actual_bounds`, `OAI_MetricKMedian_CopyState_assignment_copies`, `OAI.MetricKMedian.CopyState.round_backup`, `OAI.MetricKMedian.CopyState.unbalanced_count_change`, `OAI.MetricKMedian.CopyState.unbalanced_small_change`, `OAI.MetricKMedian.FixedBatch.masked_biased_linear_bound`, `OAI.MetricKMedian.FixedBatch.masked_mass_sum`, `OAI.MetricKMedian.FixedBatch.masked_total_bound`, `OAI.MetricKMedian.Preparation.exists_rational_all_parameters`, `OAI.MetricKMedian.RationalBatchData.proposal_count_tail` and `OAI.MetricKMedian.Taper.GraphData.drift`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib

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

noncomputable def d (s : Bool) : ℝ := if s then 2/5 else 13/25
noncomputable def hh (s : Bool) : ℝ := 8/5 + (2/5) * d s
noncomputable def uZero (s : Bool) : ℝ := d s / hh s
noncomputable def T1 (p x : ℝ) : ℝ :=
  1-p-(28/25)*p*(1+x)+(2/5)*p^2*(1-x)*(1+x)
noncomputable def T2 (p x : ℝ) : ℝ :=
  ((1-p)^2-(19/50)*p*(1-x)+p*x)*(1+x)-2*x*(1-p)
noncomputable def Yprime (p k x : ℝ) : ℝ :=
  1-k+p*((8/5)*(1-x)^2-2)

end MetricKMedian.ScalarTransfer


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalBrackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset

theorem same_interval_cuts (B : Finset ℚ) (a b : ℚ)
    (hgap : ∀ q ∈ B, q ≤ a ∨ b ≤ q) (x y : ℝ)
    (hx : (a:ℝ) < x ∧ x < (b:ℝ)) (hy : (a:ℝ) < y ∧ y < (b:ℝ)) :
    ∀ q ∈ B, (x ≤ (q:ℝ) ↔ y ≤ (q:ℝ)) ∧ ((q:ℝ) ≤ x ↔ (q:ℝ) ≤ y) := by
  intro q hq
  rcases hgap q hq with hq | hq
  · have hq' : (q:ℝ) ≤ a := by exact_mod_cast hq
    exact ⟨iff_of_false (not_le_of_gt (hq'.trans_lt hx.1))
      (not_le_of_gt (hq'.trans_lt hy.1)),iff_of_true (hq'.trans hx.1.le) (hq'.trans hy.1.le)⟩
  · have hq' : (b:ℝ) ≤ q := by exact_mod_cast hq
    exact ⟨iff_of_true (hx.2.le.trans hq') (hy.2.le.trans hq'),
      iff_of_false (not_le_of_gt (hx.2.trans_le hq')) (not_le_of_gt (hy.2.trans_le hq'))⟩

end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_NearestAssignmentGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {I T X : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [PseudoMetricSpace X]

noncomputable def relevantRadius (c L R : ℝ) : ℝ := if 0 < c then L else R

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparationParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation

noncomputable def parameterEnvelopeFar (a : ℝ) : ℝ :=
  max (1/(1-a)) (1+2*a/(1-a^2-a))*((1+a)/(1-a))+(a^2+1+a)*a^5
noncomputable def parameterEnvelopeNear (a : ℝ) : ℝ :=
  1/(1-a)+9*(a^2+1+a)*a^2
noncomputable def parameterEnvelope (a : ℝ) : ℝ :=
  max (parameterEnvelopeFar a) (parameterEnvelopeNear a)/(1-8*a^8)

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparationStars
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

 theorem target_card_sum {E : Type} [Fintype E] (D : E → Finset T) (w : E → ℝ) :
    (∑ e, ((D e).card:ℝ)*w e)=∑ t, ∑ e, if t ∈ D e then w e else 0 := by
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  simp only [sum_ite_mem,univ_inter,sum_const,nsmul_eq_mul]

end MetricKMedian.Preparation.SupplierStars
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_SourceBalance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SourceBalance
open Finset
variable {I : Type*} [Fintype I]

noncomputable def negative (m : I → ℝ) : Finset I := univ.filter (fun i => 1 < m i)
noncomputable def nonzero (m : I → ℝ) : Finset I := univ.filter (fun i => m i ≠ 1)
noncomputable def amount (m : I → ℝ) : ℝ := ∑ i, max (1-m i) 0

end MetricKMedian.SourceBalance
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalBatchLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.PhysicalBatchLaw
open Finset
variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable def unbalanced (Z : Finset E) (ω : E → Bool) : Finset E :=
  univ.filter (fun e => ω e=true ∧ e ∉ Z)

end MetricKMedian.PhysicalBatchLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CountSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SourceBalance
open Finset
variable {I : Type*} [Fintype I]

noncomputable def bias (m : I → ℝ) (p φ : ℝ) (i : I) : ℝ :=
  if 1 < m i then (1+φ)*p else p

end MetricKMedian.SourceBalance

end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n m : ℕ}

def pairSet (S : Fin m → Finset (Fin n)) (a : Fin (m*m)) : Finset (Fin n) :=
  S (finProdFinEquiv.symm a).1 ∪ S (finProdFinEquiv.symm a).2

def pairCoefficient (c : Fin m → ℚ) (a : Fin (m*m)) : ℚ :=
  c (finProdFinEquiv.symm a).1*c (finProdFinEquiv.symm a).2

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

noncomputable def marginal (P d r : ℝ) : ℝ := min 1 (max (1-r*d) 0/P)

theorem marginal_nonneg {P d r : ℝ} (hP : 0 < P) : 0 ≤ marginal P d r :=
  le_min (by norm_num) (div_nonneg (le_max_right _ _) hP.le)

theorem marginal_le_one (P d r : ℝ) : marginal P d r ≤ 1 := min_le_left _ _

theorem marginal_one {P d r : ℝ} (hP : 0 < P) (h : r*d ≤ 1-P) : marginal P d r=1 := by
  apply min_eq_left
  apply (le_div_iff₀ hP).mpr
  have hh := le_max_left (1-r*d) 0
  linarith only [h, hh]

theorem marginal_zero {P d r : ℝ} (h : 1 ≤ r*d) : marginal P d r=0 := by
  simp only [marginal, max_eq_right (by linarith : 1-r*d ≤ 0), zero_div]
  norm_num

theorem marginal_at_zero_distance {P r : ℝ} (hP : 0 < P) (hP1 : P ≤ 1) : marginal P 0 r=1 := by
  apply marginal_one hP
  simpa only [mul_zero] using sub_nonneg.mpr hP1

variable {I : Type*} [Fintype I]

noncomputable def mass (g P : ℝ) (d : I → ℝ) (r : ℝ) : ℝ := ∑ i, g*marginal P (d i) r

noncomputable def colocatedMass (g : ℝ) (d : I → ℝ) : ℝ := ∑ i, if d i=0 then g else 0

theorem continuous_mass {g P : ℝ} {d : I → ℝ} : Continuous (mass g P d) := by
  unfold mass marginal
  fun_prop

end MetricKMedian.Taper
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

def target (q : Fin n → Fin m → ℚ) (t : ℕ) (h : Fin n) (i : Fin m) : ℚ :=
  if i.val<t then q h i else 0

theorem target_succ_eq (q : Fin n → Fin m → ℚ) (t : ℕ) (ht : t < m) (h : Fin n) :
    target q (t+1) h ⟨t,ht⟩=q h ⟨t,ht⟩ := by simp [target]

theorem target_succ_ne (q : Fin n → Fin m → ℚ) (t : ℕ) (ht : t < m)
    (h : Fin n) (i : Fin m) (hi : i≠⟨t,ht⟩) : target q (t+1) h i=target q t h i := by
  have hv : i.val≠t := fun he => hi (Fin.ext he)
  have hh : i.val<t+1 ↔ i.val<t := by omega
  simp only [target,hh]

end MetricKMedian.SparseGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_RepresentativeProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.RationalRepresentatives.Program
open Finset Polynomial

structure Input where
  n : ℕ
  R : Fin n → ℚ
  d : Fin n → Fin n → ℚ
  M : ℚ
  U : Finset (Fin n)
abbrev Cut (x : Input) := Finset (Fin x.n) × Finset (Fin x.n)
structure State where
  input : Input
  cut : Cut input
end MetricKMedian.Preparation.RationalRepresentatives.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_SupplierAllocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {I T E : Type} [Fintype I] [DecidableEq I]
  [Fintype T] [DecidableEq T] [Fintype E]

def supplierOutside (σ : E → I ⊕ T) (q : E → ℝ) (i : I) : ℝ :=
  ∑ e, if σ e=Sum.inl i then q e else 0

def supplierBundle (σ : E → I ⊕ T) (q : E → ℝ) (t : T) : ℝ :=
  ∑ e, if σ e=Sum.inr t then q e else 0

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_TaperGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I X : Type*} [Fintype I] [DecidableEq I] [PseudoMetricSpace X]

structure GraphData (Δ : ℕ) (g P : ℝ) (location : I → X) (own : I → Finset I) where
  radius : I → ℝ
  marginal : I → I → ℝ
  radius_nonneg : ∀ i, 0 ≤ radius i
  marginal_nonneg : ∀ h i, 0 ≤ marginal h i
  marginal_le_one : ∀ h i, marginal h i ≤ 1
  incoming_mass : ∀ i, ∑ h, g*marginal h i=1
  incoming_count : ∀ i, ∑ h, marginal h i=Δ
  own_certain : ∀ i h, h ∈ own i → marginal h i=1
  lower : ∀ h i, marginal h i < 1 →
    radius i*(1-P*marginal h i) ≤ dist (location i) (location h)
  upper : ∀ h i, 0 < marginal h i →
    dist (location i) (location h) ≤ radius i*(1-P*marginal h i)
  minimal : ∀ i R, 0 < R →
    1 ≤ mass g P (fun h => dist (location i) (location h)) (1/R) → radius i ≤ R

def GraphData.Good {Δ : ℕ} {g P : ℝ} {location : I → X} {own : I → Finset I}
    (D : GraphData Δ g P location own) (G : I → Finset I) : Prop :=
  (∀ i, (G i).card=Δ) ∧ (∀ i, own i ⊆ G i) ∧
    (∀ h i, h ∈ G i → 0 < D.marginal h i)

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_RationalThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def deletionChoices {I : Type} [DecidableEq I] (T : Finset I) (c : ℕ) : Finset (Finset I) :=
  (range (c+1)).biUnion (fun m => T.powersetCard m)

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_BoundedEnumerationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section
namespace MetricKMedian.Reduction.Enumeration
open Finset
def words {α : Type} : ℕ → List α → List (List α)
  | 0,_ => [[]]
  | c+1,xs => []::xs.flatMap (fun a => (words c xs).map (List.cons a))
end MetricKMedian.Reduction.Enumeration
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_TargetSubsetProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseTargetSubset.Program
structure Input where
  n : ℕ
  D : Finset (Fin n)
  q : ℚ
  feasible : 0≤q ∧ q≤1
end MetricKMedian.SparseTargetSubset.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_ExceptionalStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]

noncomputable def upperBit (q : ℝ) : ℝ := if 0 < q then 1 else 0

 theorem upperBit_bounds {q : ℝ} (_hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    q ≤ upperBit q ∧ upperBit q ≤ 1 := by
  unfold upperBit
  split_ifs with h
  · exact ⟨hq1, le_rfl⟩
  · exact ⟨le_of_not_gt h, zero_le_one⟩

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseStarActivation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseStarActivation
open Finset
variable {n m : ℕ}

def upper (q : ℚ) : ℚ := if 0 < q then 1 else 0

end MetricKMedian.SparseStarActivation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_StarActivationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.SparseStarActivation.Program

def dummy : SparseTargetSubset.Program.Input := ⟨0,∅,0,by norm_num⟩
end MetricKMedian.SparseStarActivation.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_OuterLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseOuterLaw.Program
structure Input where
  n : ℕ
  m : ℕ
  D : Fin m → Finset (Fin n)
  c : Fin m → ℚ
  q : Fin m → ℚ
  c_unit : ∀ e,0 ≤ c e ∧ c e≤1
  q_nonnegative : ∀ e,0≤q e
end MetricKMedian.SparseOuterLaw.Program
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

def countSets (a : Fin (n+n*n)) : Finset (Fin n) :=
  (finSumFinEquiv.symm a).elim (fun i => {i})
    (fun ij => {(finProdFinEquiv.symm ij).1} ∪ {(finProdFinEquiv.symm ij).2})

def countCoefficients (b : Fin n → ℚ) (c : Fin n → Fin n → ℚ) (a : Fin (n+n*n)) : ℚ :=
  (finSumFinEquiv.symm a).elim b
    (fun ij => (1/2)*c (finProdFinEquiv.symm ij).1 (finProdFinEquiv.symm ij).2)

end MetricKMedian.SparseBernoulli
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_GridClipping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {E T Ω : Type} [Fintype E] [DecidableEq T]

theorem grid_clip {Δ : ℕ} {g : ℝ} (hg : 0 < g) (heven : Even Δ)
    (hunit : g*(Δ:ℝ)=1) (Z : ℕ) :
    min (g*(Z:ℝ)) (1/2)=g*(min Z (Δ/2):ℕ) ∧
    1-min (g*(Z:ℝ)) (1/2)=g*(Δ-min Z (Δ/2):ℕ) ∧
    (1/2:ℝ) ≤ g*(Δ-min Z (Δ/2):ℕ) ∧
    g*(Δ-min Z (Δ/2):ℕ) ≤ 1 := by
  have htwo : Δ/2+Δ/2=Δ := by
    obtain ⟨n,hn⟩ := heven
    omega
  have hhalf : g*(Δ/2:ℕ)= (1/2:ℝ) := by
    have hh : (Δ/2:ℕ)+(Δ/2:ℕ)=(Δ:ℝ) := by exact_mod_cast htwo
    have he := congrArg (fun x : ℝ => g*x) hh
    rw [mul_add,hunit] at he
    linarith only [he]
  have hle : min Z (Δ/2) ≤ Δ := (min_le_right _ _).trans (Nat.div_le_self _ _)
  have hc : min (g*(Z:ℝ)) (1/2)=g*(min Z (Δ/2):ℕ) := by
    rw [← hhalf,Nat.cast_min,mul_min_of_nonneg _ _ hg.le]
  have hm : 1-min (g*(Z:ℝ)) (1/2)=g*(Δ-min Z (Δ/2):ℕ) := by
    rw [hc,Nat.cast_sub hle,mul_sub,hunit]
  refine ⟨hc,hm,?_,?_⟩
  · rw [← hm]
    have hc' : min (g*(Z:ℝ)) (1/2) ≤ (1/2:ℝ) := min_le_right _ _
    linarith only [hc']
  · rw [← hm]
    have hz : 0 ≤ min (g*(Z:ℝ)) (1/2) := le_min (mul_nonneg hg.le (Nat.cast_nonneg _)) (by norm_num)
    linarith only [hz]

end MetricKMedian.Preparation
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

def target (q : Fin n → Fin m → ℚ) (t : ℕ) (h : Fin n) (i : Fin m) : ℚ :=
  if i.val<t then q h i else 0

theorem target_succ_eq (q : Fin n → Fin m → ℚ) (t : ℕ) (ht : t < m) (h : Fin n) :
    target q (t+1) h ⟨t,ht⟩=q h ⟨t,ht⟩ := by simp [target]

theorem target_succ_ne (q : Fin n → Fin m → ℚ) (t : ℕ) (ht : t < m)
    (h : Fin n) (i : Fin m) (hi : i≠⟨t,ht⟩) : target q (t+1) h i=target q t h i := by
  have hv : i.val≠t := fun he => hi (Fin.ext he)
  have hh : i.val<t+1 ↔ i.val<t := by omega
  simp only [target,hh]

end MetricKMedian.SparseCounts
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseOuterMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseOuterLaw
open Finset
variable {n m : ℕ}

def targetMean (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (i : Fin n) : ℚ :=
  ∑ e, if i∈D e then q e else 0

end MetricKMedian.SparseOuterLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalRetain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalRetain
open Finset

def keep : {n : ℕ} → (Fin n → ℕ) → ℕ → (Fin n → ℕ)
  | 0,_,_ => Fin.elim0
  | n+1,q,k => Fin.cons (min (q 0) k) (keep (fun i : Fin n => q i.succ) (k-min (q 0) k))

theorem le {n : ℕ} (q : Fin n → ℕ) (k : ℕ) : ∀ i, keep q k i ≤ q i := by
  induction n generalizing k with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [keep,Fin.cons_zero] using min_le_left (q 0) k
    · simpa only [keep,Fin.cons_succ] using ih (fun j => q j.succ) (k-min (q 0) k) j

theorem total {n : ℕ} (q : Fin n → ℕ) (k : ℕ) :
    (∑ i,keep q k i)=min (∑ i,q i) k := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
    simp only [keep,Fin.cons_zero,Fin.cons_succ]
    rw [ih]
    omega

end MetricKMedian.RationalRetain
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_RestrictionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Reduction.Enumeration
open Finset
 theorem mem_orderList {n : ℕ} (T : Finset (Fin n)) (i : Fin n) : i∈List.ofFn (T.orderEmbOfFin rfl) ↔ i∈T := by
  simp only [List.mem_ofFn]
  constructor
  · rintro ⟨a,rfl⟩; exact T.orderEmbOfFin_mem rfl a
  · intro hi
    have h : i ∈ Set.range (T.orderEmbOfFin rfl) := by rw [T.range_orderEmbOfFin rfl]; exact hi
    exact h
 def pairs {n : ℕ} (T : Finset (Fin n)) : List (Fin n × Fin n) :=
  (List.ofFn (T.orderEmbOfFin rfl)).flatMap (fun i => (List.ofFn (T.orderEmbOfFin rfl)).map (fun j => (i,j)))
end MetricKMedian.Reduction.Enumeration
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_RationalLocalChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def pickSingleton {X : Type*} [LinearOrder X] (K : Finset X) (w : X → ℚ) : Finset X :=
  if hK : K.Nonempty then
    let m := (K.image w).min' (hK.image w)
    let A := K.filter (fun a => w a=m)
    have hA : A.Nonempty := by
      obtain ⟨a,ha,he⟩ := mem_image.mp (min'_mem (K.image w) (hK.image w))
      exact ⟨a,mem_filter.mpr ⟨ha,he⟩⟩
    {A.min' hA}
  else ∅

end MetricKMedian.Reduction
end
end

end OAI
end


