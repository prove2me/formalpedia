-- Prove2me | Definitions.Def_OAIQ035K029
-- name    : OAIQ035K029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:59:04.536792+00:00
-- url     : https://prove2.me/theorems/f00e5055-2a46-4dab-9390-6019f30a0903
-- title:
--   Definitions bundle OAIQ035K029 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 31 declarations of OpenAI's Lean: 20 definitions, 2 inductive types or structures and 9 theorems. The definitions and types are `OAI.MetricKMedian.FiniteComparison.K`, `OAI.MetricKMedian.FiniteComparison.ScalarBounds`, `OAI.MetricKMedian.FiniteComparison.centered`, `OAI.MetricKMedian.FixedBatch.RationalParameters.CopyNearestProgram.instLinearOrderCopyFin`, `OAI.MetricKMedian.FixedBatch.RationalParameters.SelectionProgram.Input`, `OAI.MetricKMedian.FixedBatch.RationalParameters.allowance`, `OAI.MetricKMedian.FixedBatch.RationalParameters.completedGood`, `OAI.MetricKMedian.FixedBatch.RationalParameters.nearest`, `OAI.MetricKMedian.FixedBatch.RationalParameters.radius`, `OAI.MetricKMedian.FixedBatch.RationalParameters.rationalGridRoundCopyOrder`, `OAI.MetricKMedian.FixedBatch.RationalParameters.taperAt`, `OAI.MetricKMedian.IntegerBranching.branch`, `OAI.MetricKMedian.RationalLaw.real`, `OAI.MetricKMedian.RationalPhysicalKernel.HistoryProgram.Hist`, `OAI.MetricKMedian.RationalPhysicalKernel.completed`, `OAI.MetricKMedian.SparseBernoulli.Program.qr`, `OAI.MetricKMedian.SparseIntegerLaw.BinarySparse.bindData`, `OAI.MetricKMedian.SparseIntegerLaw.branch`, `OAI.MetricKMedian.SparseIntegerLaw.dirac`, `OAI.MetricKMedian.SparseIntegerLaw.real`, `OAI.MetricKMedian.SparseIntegerLaw.realIndex`, `OAI.MetricKMedian.SparseIntegerLaw.trim`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Analysis_FiniteAverages`, `KMedian_Geometry_IntegerBranching`, `KMedian_Geometry_RationalGridRound`, `KMedian_Geometry_RationalHistoryCompletion`, `KMedian_Geometry_RationalHistorySelection`, `KMedian_Geometry_RationalParameterizedHistory`, `KMedian_Probability_BernoulliStepProgram`, `KMedian_Probability_PushforwardLaw`, `KMedian_Process_CopyNearestProgram`, `KMedian_Process_PhysicalHistoriesProgram`, `KMedian_Programs_HistorySelectionProgram`, `KMedian_Sparse_SparseAlgorithm`, `KMedian_Sparse_SparseBindProgram`, `KMedian_Sparse_SparseIntegerLaw`, `KMedian_Sparse_SparseMap`, `KMedian_Sparse_SparseMarginalTools`, `KMedian_Sparse_SparseRealLaw`.
--
--   **Imports.** It imports the bundles `OAIQ035K014`, `OAIQ035K015`, `OAIQ035K016`, `OAIQ035K017` and `OAIQ035K019` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K039`, `OAIQ035K040`, `OAIQ035K041`, `OAIQ035K042`, `OAIQ035K043`, `OAIQ035K045` and `OAIQ035K062`; the statement `OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds`; the proofs of `OAI.MetricKMedian.GraphComparison.unnormalized_drift_le` and `OAI.MetricKMedian.WeightedRounding.exact_law`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K014
import Definitions.Def_OAIQ035K015
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K017
import Definitions.Def_OAIQ035K019

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_FiniteAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.FiniteComparison

noncomputable def K (p z : ℝ) (b : Bool → ℝ) (s : Bool) (r : ℝ) : ℝ :=
  C p s - k p s - b s * r + (8 / 5) * z

noncomputable def centered (p m a z : ℝ) (b : Bool → ℝ)
    (s : Bool) (D q Z : ℝ) : ℝ :=
  (m * D + b s * (D + 1)) * q +
    D * (C p s * psi p q + a * (1 - q) - C p s) -
    ((2 / 5) * D + 8 / 5) * z - C p s + k p s -
    (k p s - (C p s * psi p q - (1 - q))) * Z

structure ScalarBounds (p m a z h : ℝ) (b : Bool → ℝ) : Prop where
  p_nonneg : 0 ≤ p
  p_le_half : p ≤ 1 / 2
  m_nonneg : 0 ≤ m
  z_nonneg : 0 ≤ z
  h_nonneg : 0 ≤ h
  h_le : h ≤ 197 / 500
  b_nonneg : ∀ s, 0 ≤ b s
  first : ∀ s r, 0 < r → r ≤ 1 →
    m + b s - (2 / 5) * z / r ≤ C p s * (1 - p) / (1 - p * r)
  linear : ∀ s r, 0 ≤ r → r ≤ 1 →
    0 ≤ L p m z b s r ∧ 0 < K p z b s r ∧
      d s * G p m a z b s r ≤ K p z b s r
  charge : ∀ s r, 0 ≤ r → r ≤ 1 →
    0 ≤ ((C p s * H h s - b s) * r + (8 / 5) * z) * M p a s r +
      (C p s - k p s - C p s * H h s * r) * L p m z b s r
  type_zero : ∀ s q, 0 ≤ q → q ≤ 1 →
    h ≤ C p s - k p s + (8 / 5) * z - b s * q +
      (13 / 25) * (k p s - (C p s * psi p q - (1 - q)))
  type_one : ∀ s, 1 / 4 ≤ C p s - k p s + (8 / 5) * z - b s

end MetricKMedian.FiniteComparison


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_IntegerBranching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerBranching
open Finset
variable {n : ℕ}

theorem branchNumerator_nonneg (p : Fin n → ℚ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (i : Fin n) (b : Fin 2) :
    0 ≤ branchNumerator p i b := by
  have hD : (0:ℚ) < RationalScaling.denominator p := by
    exact_mod_cast RationalScaling.denominator_pos p
  have hA0 : (0:ℤ) ≤ RationalScaling.numerator p i := by
    have hh := mul_nonneg (hp i).1 hD.le
    rw [← RationalScaling.numerator_cast] at hh
    exact_mod_cast hh
  have hA1 : RationalScaling.numerator p i ≤ RationalScaling.denominator p := by
    have hh := mul_le_mul_of_nonneg_right (hp i).2 hD.le
    rw [one_mul,← RationalScaling.numerator_cast] at hh
    exact_mod_cast hh
  dsimp only [branchNumerator]
  split_ifs
  · exact hA0
  · exact sub_nonneg.mpr hA1

def branch (μ : IntegerLaw (Fin n)) (p : Fin n → ℚ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) : IntegerLaw (Fin n × Fin 2) where
  denominator := μ.denominator*RationalScaling.denominator p
  denominator_pos := mul_pos μ.denominator_pos (RationalScaling.denominator_pos p)
  numerator := let v := Vector.ofFn (fun i => Vector.ofFn (fun b =>
    μ.numerator i*branchNumerator p i b))
    fun a => v[a.1.val][a.2.val]
  numerator_nonneg a := by
    simp only [Vector.getElem_ofFn]
    exact mul_nonneg (μ.numerator_nonneg _) (branchNumerator_nonneg p hp _ _)
  total := by
    simp only [Vector.getElem_ofFn,Fin.eta]
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two,branchNumerator]
    norm_num only [show (1:Fin 2) ≠ 0 by decide,ite_true,ite_false]
    simp only [mul_sub,add_sub_cancel,← sum_mul,μ.total]

end MetricKMedian.IntegerBranching

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseIntegerLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian
open Finset

namespace SparseIntegerLaw
variable {α : Type}

def trim (μ : SparseIntegerLaw α) : SparseIntegerLaw α where
  length := μ.law.support.card
  states := Vector.ofFn (fun i => μ.states[(μ.law.support.orderEmbOfFin rfl i).val])
  law := μ.law.trim

end SparseIntegerLaw
end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseAlgorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

def branch (μ : SparseIntegerLaw α) (p : α → ℚ)
    (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (next : α → Fin 2 → α) : SparseIntegerLaw α where
  length := μ.length*2
  states := Vector.ofFn (fun i => next
    μ.states[(finProdFinEquiv.symm i).1.val] (finProdFinEquiv.symm i).2)
  law := (IntegerBranching.branch μ.law (fun i => p μ.states[i.val])
    (fun i => hp μ.states[i.val])).reindex finProdFinEquiv

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseMarginalTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

 def dirac (a : α) : SparseIntegerLaw α where
  length := 1
  states := Vector.replicate 1 a
  law := {
    denominator := 1
    denominator_pos := by norm_num
    numerator := fun _ => 1
    numerator_nonneg := fun _ => by norm_num
    total := by simp }

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseRealLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian
namespace RationalLaw
variable {α : Type} [Fintype α]

noncomputable def real (μ : RationalLaw α) : FiniteLaw α where
  weight a := (μ.weight a:ℝ)
  nonneg a := by exact_mod_cast μ.nonneg a
  total := by exact_mod_cast μ.total

@[simp] theorem real_expect (μ : RationalLaw α) (f : α → ℚ) :
    μ.real.expect (fun a => (f a:ℝ))=((∑ a, μ.weight a*f a:ℚ):ℝ) := by
  simp only [FiniteLaw.expect,real,Rat.cast_sum,Rat.cast_mul]

end RationalLaw

namespace SparseIntegerLaw
variable {α : Type}

noncomputable def realIndex (μ : SparseIntegerLaw α) : FiniteLaw (Fin μ.length) :=
  μ.law.rational.real

@[simp] theorem realIndex_expect (μ : SparseIntegerLaw α) (f : α → ℚ) :
    μ.realIndex.expect (fun i => (f μ.states[i.val]:ℝ))=(μ.moment f:ℝ) := by
  exact μ.law.rational.real_expect (fun i => f μ.states[i.val])

noncomputable def real [Fintype α] [DecidableEq α] (μ : SparseIntegerLaw α) : FiniteLaw α :=
  μ.realIndex.map (fun i => μ.states[i.val])

@[simp] theorem real_expect [Fintype α] [DecidableEq α] (μ : SparseIntegerLaw α) (f : α → ℚ) :
    μ.real.expect (fun a => (f a:ℝ))=(μ.moment f:ℝ) := by
  rw [real,FiniteLaw.expect_map,realIndex_expect]

end SparseIntegerLaw
end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
variable {α β : Type}

@[simp] theorem map_states (μ : SparseIntegerLaw α) (f : α → β) (i : Fin (μ.map f).length) :
    (μ.map f).states[i.val]=f μ.states[i.val] := by
  simp only [map,Vector.getElem_map]

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalHistoryCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential CopyState Completion.Rational
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j Δ : ℕ}

def completed (d : Fin j → F → ℚ) (R : Fin j → ℚ)
    (B : Fin j → Finset (Copy (F := F) Δ)) (hB : ∀ c, (B c).Nonempty)
    (g β : ℚ) (z : SparseHistories.History (State F Δ g β)) : Finset F :=
  Completion.Rational.output d R z.1.1 B hB

end MetricKMedian.RationalPhysicalKernel
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalParameterizedHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                    
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
variable {τ : ℝ} (q : RationalParameters τ)

theorem probabilityQ_pos : 0 < q.probabilityQ := by
  have hh := q.hpos
  have hg := q.gpos
  exact_mod_cast (show 0 < 2*(q.h:ℝ)*(q.g:ℝ) by positivity)

theorem probabilityQ_le : (1+q.φ)*q.probabilityQ ≤ 1 := by
  exact_mod_cast q.probability

def taperAt (t : ℕ) : ℚ := if ht : t<q.T then q.taper ⟨t,ht⟩ else 1/2

def allowance : ℚ := (q.T:ℚ)*(4/(q.g*q.β))

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalHistorySelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
variable {τ : ℝ} (q : RationalParameters τ)
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j : ℕ}

def completedGood (d : Fin j → F → ℚ) (R : Fin j → ℚ)
    (A : Finset (Copy (F := F) q.Δ)) (B : Fin j → Finset (Copy (F := F) q.Δ))
    (hB : ∀ c, (B c).Nonempty) (z : SparseHistories.History (State F q.Δ q.g q.β)) : Bool :=
  decide ((completed d R B hB q.g q.β z).Nonempty ∧
    ((completed d R B hB q.g q.β z).card:ℚ) ≤ q.g*A.card+q.allowance)

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_PushforwardLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
open Finset
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ]

 theorem support_map (μ : FiniteLaw Ω) (f : Ω → Ξ) (ξ : Ξ)
    (h : 0 < (μ.map f).weight ξ) : ∃ ω, 0 < μ.weight ω ∧ f ω=ξ := by
  exact μ.property_map f (fun ξ => ∃ ω, 0 < μ.weight ω ∧ f ω=ξ)
    (fun ω hω => ⟨ω,hω,rfl⟩) ξ h

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalGridRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
open Preparation.RationalNearest
variable {τ : ℝ} (q : RationalParameters τ)
variable {F X : Type} [LinearOrder F] [PseudoMetricSpace X] {j : ℕ}
local instance rationalGridRoundCopyOrder : LinearOrder (Copy (F := F) q.Δ) := copyOrder

def nearest (d : Fin j → F → ℚ) (A : Finset (Copy (F := F) q.Δ)) :
    Fin j → Finset (Copy (F := F) q.Δ) := fun c => takeNearest (fun a => d c a.1) q.Δ A

theorem nearest_nonempty (d : Fin j → F → ℚ) (A : Finset (Copy (F := F) q.Δ))
    (hA : q.Δ ≤ A.card) (c : Fin j) : (q.nearest d A c).Nonempty := by
  apply card_pos.mp
  change 0 < (takeNearest (fun a : Copy (F := F) q.Δ => d c a.1) q.Δ A).card
  rw [(takeNearest_spec (fun a : Copy (F := F) q.Δ => d c a.1) q.Δ A hA).2.1]
  exact q.Δpos

def radius (d : Fin j → F → ℚ) (A : Finset (Copy (F := F) q.Δ))
    (hA : q.Δ ≤ A.card) (c : Fin j) : ℚ :=
  ((q.nearest d A c).image (fun a => d c a.1)).max' ((q.nearest_nonempty d A hA c).image _)

end MetricKMedian.FixedBatch.RationalParameters
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
abbrev qr := encodeList Ratio.encode

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyNearestProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.FixedBatch.RationalParameters.CopyNearestProgram
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open RationalPhysicalKernel RationalPhysicalKernel.CopyList
open SparseGraph.ListOperation (Row Table setView indices)
variable {τ : ℝ} (q : RationalParameters τ)
local instance instLinearOrderCopyFin {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder

end MetricKMedian.FixedBatch.RationalParameters.CopyNearestProgram
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

def bindData (x : LawData × List (Data A)) : Data A :=
  ((IntegerList.denominator (jointWeights x),IntegerList.numerators (jointWeights x)),
    x.2.flatMap Prod.snd)

end MetricKMedian.SparseIntegerLaw.BinarySparse
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

abbrev Hist (x : Context) := SparseHistories.History (State (Fin x.f) x.Δ x.g x.β)
end MetricKMedian.RationalPhysicalKernel.HistoryProgram
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_HistorySelectionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.FixedBatch.RationalParameters.SelectionProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
open RationalPhysicalKernel
variable {τ : ℝ} (q : RationalParameters τ)

structure Input extends Completion.Rational.Program.Input q.Δ where
  d₀ : Fin f → Fin f → ℚ
end MetricKMedian.FixedBatch.RationalParameters.SelectionProgram
end

end OAI
end


