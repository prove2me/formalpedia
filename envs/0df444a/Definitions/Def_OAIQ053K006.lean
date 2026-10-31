-- Prove2me | Definitions.Def_OAIQ053K006
-- name    : OAIQ053K006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:54:05.26377+00:00
-- url     : https://prove2.me/theorems/43d083a3-52a1-40d2-bf6a-2245958fba2f
-- title:
--   Definitions bundle OAIQ053K006 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 130 declarations of OpenAI's Lean: 86 definitions, 11 inductive types or structures and 33 theorems. The definitions and types are `OAI.MetricKMedian.CountGeometry.overlap`, `OAI.MetricKMedian.CountStatistic.bit`, `OAI.MetricKMedian.CountStatistic.statistic`, `OAI.MetricKMedian.Coverage.BlockCode`, `OAI.MetricKMedian.Coverage.Input`, `OAI.MetricKMedian.Coverage.Input.Perfect`, `OAI.MetricKMedian.Coverage.Input.Point`, `OAI.MetricKMedian.Coverage.Input.Sound`, `OAI.MetricKMedian.Coverage.Input.accepts`, `OAI.MetricKMedian.Coverage.Input.chosenFacilities`, `OAI.MetricKMedian.Coverage.Input.client`, `OAI.MetricKMedian.Coverage.Input.comparisonCost`, `OAI.MetricKMedian.Coverage.Input.covered`, `OAI.MetricKMedian.Coverage.Input.encode`, `OAI.MetricKMedian.Coverage.Input.facility`, `OAI.MetricKMedian.Coverage.Input.pointDistance`, `OAI.MetricKMedian.Coverage.Input.selected`, `OAI.MetricKMedian.Coverage.Input.selectedMask`, `OAI.MetricKMedian.Coverage.Input.toMedian`, `OAI.MetricKMedian.Coverage.PartitionParameters`, `OAI.MetricKMedian.Coverage.Partitions.active`, `OAI.MetricKMedian.Coverage.Partitions.avoid`, `OAI.MetricKMedian.Coverage.Partitions.avoidEquiv`, `OAI.MetricKMedian.Coverage.Partitions.hit`, `OAI.MetricKMedian.Coverage.ProjectionInput`, `OAI.MetricKMedian.Coverage.ProjectionInput.Block`, `OAI.MetricKMedian.Coverage.ProjectionInput.Perfect`, `OAI.MetricKMedian.Coverage.ProjectionInput.Sound`, `OAI.MetricKMedian.Coverage.ProjectionInput.blockEquiv`, `OAI.MetricKMedian.Coverage.ProjectionInput.clientEquiv`, `OAI.MetricKMedian.Coverage.ProjectionInput.facilityEquiv`, `OAI.MetricKMedian.Coverage.ProjectionInput.toCoverage`, `OAI.MetricKMedian.Coverage.ProjectionInput.width`, `OAI.MetricKMedian.Coverage.ProjectionRaw`, `OAI.MetricKMedian.Coverage.ProjectionRaw.edge`, `OAI.MetricKMedian.Coverage.ProjectionRaw.incident`, `OAI.MetricKMedian.Coverage.ProjectionRaw.lefts`, `OAI.MetricKMedian.Coverage.ProjectionRaw.rights`, `OAI.MetricKMedian.Coverage.ProjectionRaw.test`, `OAI.MetricKMedian.Coverage.ProjectionSystem` and 57 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Analysis_FiniteAverages`, `KMedian_Analysis_RowComparison`, `KMedian_Analysis_ScalarTransfer`, `KMedian_Geometry_NearestReindex`, `KMedian_Geometry_SortedListEncoding`, `KMedian_Hardness_Analysis`, `KMedian_Hardness_Constants`, `KMedian_Hardness_Coverage`, `KMedian_Hardness_Encoding`, `KMedian_Hardness_Lists`, `KMedian_Hardness_Partition`, `KMedian_Hardness_Projection`, `KMedian_Hardness_ProjectionEncoding`, `KMedian_Hardness_ProjectionInput`, `KMedian_Hardness_Sampling`, `KMedian_Instance`, `KMedian_Preparation_PreparedScanProgram`, `KMedian_Preparation_RepresentativeGeometry`, `KMedian_Probability_BernoulliBatches`, `KMedian_Probability_BernoulliStepProgram`, `KMedian_Probability_FiniteClipping`, `KMedian_Process_BatchProposalProgram`, `KMedian_Process_CountGeometry`, `KMedian_Process_FiniteGraph`, `KMedian_Process_PhysicalPotential`, `KMedian_Process_QuadraticCount`, `KMedian_Process_RoundCountsProgram`, `KMedian_Process_RoundingRunProgram`, `KMedian_Process_TaperGraphProgram`, `KMedian_Process_TaperReindex`, `KMedian_Programs_BoundedEnumerationProgram`, `KMedian_Programs_CardinalRoundProgram`, `KMedian_Programs_GraphLawProgram`, `KMedian_Programs_PivotListProgram`, `KMedian_Rounding_GridRoundingProgram`.
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K018`, `OAIQ053K019`, `OAIQ053K020`, `OAIQ053K021`, `OAIQ053K022`, `OAIQ053K024`, `OAIQ053K026` and `OAIQ053K027`; the statements `OAI.MetricKMedian.Certificates.k_envelope_s53`, `OAI.MetricKMedian.Coverage.ProjectionSystem.coverage_agreement_bound_s53`, `OAI.MetricKMedian.Coverage.ProjectionSystem.coverage_bound_s53`, `OAI.MetricKMedian.FiniteComparison.centering_gap_nonneg_s53` and `OAI.MetricKMedian.FiniteComparison.finite_comparison_s53`; the proofs of `OAI.MetricKMedian.Certificates.k_envelope_s53`, `OAI.MetricKMedian.Coverage.ProjectionSystem.coverage_agreement_bound_s53`, `OAI.MetricKMedian.Coverage.ProjectionSystem.coverage_bound_s53` and `OAI.MetricKMedian.FiniteComparison.centering_gap_nonneg_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold

section
-- module Solutions.OAIQ053_KM.KMedian_Analysis_FiniteAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteComparison

noncomputable def psi (p q : ℝ) : ℝ := (1 - q) / (1 - p * q)

noncomputable def kZero (p : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - p)) / (1 + Real.sqrt (1 - p))

noncomputable def kappa (p s q : ℝ) : ℝ :=
  (1 - p * s) * psi p q - (1 - q)

end MetricKMedian.FiniteComparison

namespace MetricKMedian.FiniteComparison

noncomputable def average {I : Type*} [Fintype I] (π f : I → ℝ) : ℝ :=
  ∑ i, π i * f i

noncomputable def C (p : ℝ) (s : Bool) : ℝ := if s then 1 - p else 1
noncomputable def k (p : ℝ) (s : Bool) : ℝ := if s then 0 else kZero p
noncomputable def H (h : ℝ) (s : Bool) : ℝ := if s then 1 / 4 else h
noncomputable def d (s : Bool) : ℝ := if s then 2 / 5 else 13 / 25

noncomputable def K (p z : ℝ) (b : Bool → ℝ) (s : Bool) (r : ℝ) : ℝ :=
  C p s - k p s - b s * r + (8 / 5) * z
noncomputable def L (p m z : ℝ) (b : Bool → ℝ) (s : Bool) (r : ℝ) : ℝ :=
  (C p s - m - b s) * r + (2 / 5) * z
noncomputable def M (p a : ℝ) (s : Bool) (r : ℝ) : ℝ :=
  (1 - r) * a + C p s * p * r
noncomputable def G (p m a z : ℝ) (b : Bool → ℝ) (s : Bool) (r : ℝ) : ℝ :=
  M p a s r - L p m z b s r

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

namespace MetricKMedian.FiniteComparison

noncomputable def rowValue {I : Type*} [Fintype I] (π Z q : I → ℝ)
    (p m a z : ℝ) (b : Bool → ℝ) (s : Bool) (D R : ℝ) : ℝ :=
  C p s * (1 - average π q) * R +
    (m * D + b s * (D + 1)) * average π q - C p s * (D + 1) -
    average π (fun t => (1 - q t) * max (Z t - a * D) 0) -
    ((2 / 5) * D + 8 / 5) * z

end MetricKMedian.FiniteComparison


end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Analysis_RowComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.FiniteComparison

noncomputable def uprime (p m z : ℝ) (b : Bool → ℝ) (s : Bool) (D r : ℝ) : ℝ :=
  ((m * D + b s * (D + 1)) * r - ((2 / 5) * D + 8 / 5) * z) / (C p s * r)

end MetricKMedian.FiniteComparison

namespace MetricKMedian.FiniteComparison

noncomputable def rawRow {I : Type*} [Fintype I] (π Z q : I → ℝ)
    (p m y s D R : ℝ) : ℝ :=
  (1 - p * s) * (1 - average π q) * R +
    average π q * (m * D + (2 - s) * p * y * (D + 1)) -
    (1 - p * s) * (D + 1) -
    average π (fun t => (1 - q t) * max (Z t - (1 + m + 2 * p * y) * D) 0)

noncomputable def endpoint (s : Bool) : ℝ := if s then 1 else 0

end MetricKMedian.FiniteComparison


end
end

end OAI
end

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

noncomputable def bit (s : Bool) : ℝ := if s then 1 else 0

end MetricKMedian.ScalarTransfer


end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_SortedListEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.EncodingLists
open Finset

theorem sorted_enum {α : Type} [LinearOrder α] (s : Finset α) :
    List.ofFn (fun i : Fin s.card => (s.orderIsoOfFin rfl i).val)=s.sort := by
  rw [List.ofFn_eq_map]
  exact s.listMap_orderEmbOfFin_finRange rfl

theorem filter_range {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    (List.finRange n).filter (fun i => decide (p i))=(univ.filter p).sort := by
  apply List.SortedLT.eq_of_mem_iff
  · exact ((List.sortedLT_finRange n).pairwise.filter _).sortedLT
  · exact (univ.filter p).sortedLT_sort
  · intro i
    simp only [List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq,mem_sort,mem_filter,mem_univ]

theorem map_filter_enum {n : ℕ} {α : Type} (f : Fin n → α) (p : Fin n → Prop) [DecidablePred p] :
    ((List.finRange n).filter (fun i => decide (p i))).map f =
      List.ofFn (fun i : Fin (univ.filter p).card => f ((univ.filter p).orderIsoOfFin rfl i).val) := by
  rw [filter_range,← sorted_enum,List.map_ofFn]
  rfl

end MetricKMedian.EncodingLists
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliBatches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian
namespace FiniteLaw
variable {I : Type*} [Fintype I] [DecidableEq I]

def coinWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p

@[simp] theorem coinWeight_true (p : ℝ) : coinWeight p true = p := rfl
@[simp] theorem coinWeight_false (p : ℝ) : coinWeight p false = 1-p := rfl

theorem coinWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ coinWeight p b := by cases b <;> simp [hp, hp1, sub_nonneg]

@[simp] theorem coinWeight_total (p : ℝ) : ∑ b : Bool, coinWeight p b = 1 := by
  simp

noncomputable def selected (C : I → Finset I) (ω : I → Bool) : Finset I :=
  Finset.univ.filter (fun i => ω i = true ∧ ∀ j ∈ C i, ω j = false)

end FiniteLaw
end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_PivotListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.IntegerLaw.ListPivot
open Function Finset
abbrev Entry := ℤ × ℤ

end MetricKMedian.IntegerLaw.ListPivot
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential

variable {I : Type*}

noncomputable def retained (a dh : ℝ) (d : I → ℝ) (physicalSurvivors : Finset I) : Finset I :=
  physicalSurvivors.filter (fun i => a * d i < dh)

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_FiniteGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteGraph

variable {I H : Type*} [Fintype H] [DecidableEq I] [DecidableEq H]

noncomputable def incoming (E : H → Finset I) (i : I) : Finset H :=
  Finset.univ.filter (fun h => i ∈ E h)

noncomputable def touching (E : H → Finset I) (S : Finset I) : Finset H :=
  S.biUnion (incoming E)

noncomputable def conflicts (E : H → Finset I) (balanced : Finset H) (h : H) : Finset H :=
  (touching E (E h) ∩ balanced).erase h

end MetricKMedian.FiniteGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_QuadraticCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CountStatistic
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def bit (ω : I → Bool) (i : I) : ℝ := if ω i then 1 else 0
noncomputable def statistic (b : I → ℝ) (c : I → I → ℝ) (ω : I → Bool) : ℝ :=
  (∑ i, b i*bit ω i)+(1/2)*∑ i, ∑ j, c i j*bit ω i*bit ω j

end MetricKMedian.CountStatistic
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_NearestReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.Preparation.RationalNearest
open Finset
variable {α β : Type} [LinearOrder α] [LinearOrder β]
theorem min_map (e : α ≃o β) (U : Finset α) (hU : U.Nonempty) :
    (U.map e.toEmbedding).min' (hU.map) = e (U.min' hU) := by
  apply le_antisymm
  · exact min'_le _ _ (mem_map.mpr ⟨_,min'_mem U hU,rfl⟩)
  · obtain ⟨a,ha,he⟩ := mem_map.mp (min'_mem (U.map e.toEmbedding) (hU.map))
    rw [← he]
    exact e.monotone (min'_le U a ha)
end MetricKMedian.Preparation.RationalNearest

end

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

@[instance_reducible] def pseudoMetric (I : Instance) : PseudoMetricSpace (Fin I.n) where
  dist i j := (I.distance i j:ℝ)
  dist_self i := by rw [(I.distance_eq_zero i i).mpr rfl, Rat.cast_zero]
  dist_comm i j := by rw [I.distance_symm i j]
  dist_triangle i j h := by exact_mod_cast I.distance_triangle i j h

end Instance
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Coverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Finset

structure Input where
  m : ℕ
  n : ℕ
  incident : Fin m → Fin n → Bool
  k : ℕ
  m_pos : 0 < m
  k_pos : 1 ≤ k
  k_le : k ≤ n

namespace Input

def encode (C : Input) : List Bool :=
  encodeNat C.m ++ encodeNat C.n ++ encodeNat C.k ++
    (List.ofFn (fun j : Fin C.m => List.ofFn (C.incident j))).flatten

def covered (C : Input) (S : Finset (Fin C.n)) : Finset (Fin C.m) :=
  univ.filter (fun j => ∃ i ∈ S, C.incident j i = true)

def Perfect (C : Input) : Prop :=
  ∃ S : Finset (Fin C.n), S.card ≤ C.k ∧ C.covered S = univ

def Sound (C : Input) (δ : ℝ) : Prop :=
  ∀ S : Finset (Fin C.n), S.card ≤ C.k →
    ((C.covered S).card : ℝ) ≤ (1 - 1 / Real.exp 1 + δ) * C.m

abbrev Point (C : Input) := Fin C.m ⊕ Fin C.n

def pointDistance (C : Input) : C.Point → C.Point → ℚ
  | .inl i, .inl j => if i = j then 0 else 2
  | .inr i, .inr j => if i = j then 0 else 2
  | .inl j, .inr i => if C.incident j i then 1 else 3
  | .inr i, .inl j => if C.incident j i then 1 else 3

theorem pointDistance_nonneg (C : Input) (x y : C.Point) :
    0 ≤ C.pointDistance x y := by
  cases x <;> cases y <;> simp only [pointDistance] <;> split <;> norm_num

theorem pointDistance_eq_zero (C : Input) (x y : C.Point) :
    C.pointDistance x y = 0 ↔ x = y := by
  cases x <;> cases y <;> simp only [pointDistance] <;> split <;> simp_all

theorem pointDistance_symm (C : Input) (x y : C.Point) :
    C.pointDistance x y = C.pointDistance y x := by
  cases x <;> cases y <;> simp only [pointDistance] <;> split_ifs <;> simp_all

theorem pointDistance_triangle (C : Input) (x y z : C.Point) :
    C.pointDistance x z ≤ C.pointDistance x y + C.pointDistance y z := by
  cases x <;> cases y <;> cases z <;>
    simp only [pointDistance] <;> split_ifs <;> subst_vars <;> (try simp_all) <;> norm_num

def client (C : Input) (j : Fin C.m) : Fin (C.m + C.n) :=
  finSumFinEquiv (Sum.inl j)

def facility (C : Input) (i : Fin C.n) : Fin (C.m + C.n) :=
  finSumFinEquiv (Sum.inr i)

theorem facility_injective (C : Input) : Function.Injective C.facility := by
  intro i j h
  exact Sum.inr.inj (finSumFinEquiv.injective h)

theorem client_ne_facility (C : Input) (j : Fin C.m) (i : Fin C.n) :
    C.client j ≠ C.facility i := by
  intro h
  have hh := finSumFinEquiv.injective h
  cases hh

def chosenFacilities (C : Input) (S : Finset (Fin C.n)) : Finset (Fin (C.m + C.n)) :=
  S.image C.facility

@[simp] theorem chosenFacilities_card (C : Input) (S : Finset (Fin C.n)) :
    (C.chosenFacilities S).card = S.card :=
  card_image_of_injective _ C.facility_injective

@[simp] theorem chosenFacilities_nonempty (C : Input) (S : Finset (Fin C.n)) :
    (C.chosenFacilities S).Nonempty ↔ S.Nonempty := image_nonempty

def toMedian (C : Input) : Instance where
  n := C.m + C.n
  distance x y := C.pointDistance (finSumFinEquiv.symm x) (finSumFinEquiv.symm y)
  clients := univ.image C.client
  facilities := C.chosenFacilities univ
  k := C.k
  distance_nonneg x y := C.pointDistance_nonneg _ _
  distance_eq_zero x y := (C.pointDistance_eq_zero _ _).trans finSumFinEquiv.symm.injective.eq_iff
  distance_symm x y := C.pointDistance_symm _ _
  distance_triangle x y z := C.pointDistance_triangle _ _ _
  k_pos := C.k_pos
  k_le := by simpa using C.k_le

@[simp] theorem distance_client_facility (C : Input) (j : Fin C.m) (i : Fin C.n) :
    C.toMedian.distance (C.client j) (C.facility i) =
      if C.incident j i then 1 else 3 := by
  simp [toMedian, client, facility, pointDistance]

@[simp] theorem mem_covered (C : Input) (S : Finset (Fin C.n)) (j : Fin C.m) :
    j ∈ C.covered S ↔ ∃ i ∈ S, C.incident j i = true := by
  simp [covered]

def selected (C : Input) (T : Finset (Fin (C.m + C.n))) : Finset (Fin C.n) :=
  univ.filter (fun i => C.facility i ∈ T)

@[simp] theorem selected_chosen (C : Input) (S : Finset (Fin C.n)) :
    C.selected (C.chosenFacilities S) = S := by
  ext i
  simp only [selected, chosenFacilities, mem_filter, mem_univ, true_and, mem_image]
  constructor
  · rintro ⟨j, hj, hij⟩
    exact C.facility_injective hij ▸ hj
  · intro hi
    exact ⟨i, hi, rfl⟩

end Input

end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RepresentativeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {J I X : Type*} [DecidableEq J] [PseudoMetricSpace X]

omit [DecidableEq J] [PseudoMetricSpace X] in
                                                                   
theorem outside_mass_bound [DecidableEq I] (F : Finset I) (y d : I → ℝ) {r : ℝ}
    (hy : ∀ i ∈ F, 0 ≤ y i) (hd : ∀ i ∈ F, 0 ≤ d i) :
    r*(∑ i ∈ F.filter (fun i => r < d i), y i) ≤ ∑ i ∈ F, y i*d i := by
  calc
    _ = ∑ i ∈ F.filter (fun i => r < d i), y i*r := by rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ ∑ i ∈ F.filter (fun i => r < d i), y i*d i := by
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (mem_filter.mp hi).2.le (hy i (mem_filter.mp hi).1)
    _ ≤ ∑ i ∈ F, y i*d i := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i hi _ => mul_nonneg (hy i hi) (hd i hi))

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CountGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CountGeometry
open Finset
variable {E U : Type*} [Fintype E] [DecidableEq E] [DecidableEq U]

def overlap (S : E → Finset U) (e f : E) : ℕ :=
  if e=f then 0 else (S e ∩ S f).card

end MetricKMedian.CountGeometry
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_FiniteClipping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
open Finset
variable {Ω I : Type*} [Fintype Ω] [Fintype I]

theorem half_clip_point {z m : ℝ} (hm : m ≤ 1/4) :
    z-min z (1/2) ≤ 4*(z-m)^2 := by
  by_cases hz : z ≤ 1/2
  · rw [min_eq_left hz, sub_self]
    positivity
  · rw [min_eq_right (le_of_not_ge hz)]
    nlinarith only [hm, sq_nonneg (2*(z-m)-1/4)]

theorem abs_clip_le {z c b : ℝ} (hcb : c ≤ b) : |c-min z b| ≤ |c-z| := by
  by_cases hz : z ≤ b
  · rw [min_eq_left hz]
  · rw [min_eq_right (le_of_not_ge hz), abs_of_nonpos (sub_nonpos.mpr hcb),
      abs_of_nonpos (sub_nonpos.mpr (hcb.trans (le_of_not_ge hz)))]
    linarith only [hz]

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_TaperReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                    
section
namespace MetricKMedian.Taper
open Finset
variable {I J : Type} [Fintype I] [Fintype J]

 theorem image_univ_reindex [DecidableEq ℚ] (e : I ≃ J) (f : J → ℚ) :
    univ.image (fun i => f (e i))=univ.image f := by
  ext q
  simp only [mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩; exact ⟨e i,rfl⟩
  · rintro ⟨j,rfl⟩; exact ⟨e.symm j,by rw [e.apply_symm_apply]⟩
end MetricKMedian.Taper
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliStepProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseBernoulli.Program
open Function

structure Input where
  n : ℕ
  p : Fin n → ℚ
  feasible : ∀ i, 0 ≤ p i ∧ p i ≤ 1

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingRunProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.RoundingProgram
open Function Polynomial
def coordinateBound (L : ℕ) := 2*L*L+L

end MetricKMedian.RoundingProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_CardinalRoundProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseCardinalRounding.Program
open Function
abbrev Input := SparseBernoulli.Program.Input
end MetricKMedian.SparseCardinalRounding.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_GraphLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseGraph.Program
open Function

structure QInput where
  n : ℕ
  m : ℕ
  q : Fin n → Fin m → ℚ
  feasible : ∀ h i, 0≤q h i ∧ q h i≤1

end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_TaperGraphProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.TaperGraphProgram

structure Input where
  n : ℕ
  d : Fin n → Fin n → ℚ
  own : Fin n → Finset (Fin n)
  g : ℚ
  P : ℚ
  Δ : ℕ
  positive : 0<P

end MetricKMedian.TaperGraphProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_BatchProposalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.RationalBatchData.ProposalProgram
open Finset
variable {C : Type} (I : C → Type) [∀ c, LinearOrder (I c)] [∀ c, Fintype (I c)]

structure Input where
  ctx : C
  n : ℕ
  enum : Fin n ≃o I ctx
  G : I ctx → Finset (I ctx)
  Δ : ℕ
  g : ℚ
  b : ℚ
  p : ℚ
  φ : ℚ
  hp : 0≤p
  hφ : 0≤φ
  hupper : (1+φ)*p≤1
end MetricKMedian.RationalBatchData.ProposalProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundCountsProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram
open Finset
variable {τ : ℝ}

structure Input where
  f : ℕ
  j : ℕ
  d₀ : Fin f → Fin f → ℚ
  d : Fin j → Fin f → ℚ
  n : Fin f → ℕ
end MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparedScanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram
open Finset
variable {τ : ℝ}
structure Input where
  f : ℕ
  h : ℕ
  j : ℕ
  df : Fin h → Fin h → ℚ
  dc : Fin j → Fin h → ℚ
  orig : Fin f → Fin h
  ns : List (Fin f → ℕ)
  budget : ℚ

def Input.item (x : Input) (n : Fin x.f → ℕ) : RoundCountsProgram.Input :=
  ⟨x.f,x.j,(fun a b => x.df (x.orig a) (x.orig b)),(fun c a => x.dc c (x.orig a)),n⟩
def Input.items (x : Input) := x.ns.map x.item

def dummy : RoundCountsProgram.Input := ⟨0,0,Fin.elim0,Fin.elim0,Fin.elim0⟩
end MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_GridRoundingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseGridRounding.Program

def fractionRow (q : List ℚ) : List ℚ := q.map (fun x => x-(⌊x⌋₊:ℚ))
end MetricKMedian.SparseGridRounding.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_BoundedEnumerationProgram
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
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Analysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage.Input
open Finset

def selectedMask (C : Input) (output : List Bool) : Finset (Fin C.n) :=
  univ.filter (fun i => (output[(C.facility i).val]?).getD false = true)

def comparisonCost (C : Input) (output : List Bool) : ℚ :=
  3 * (C.m : ℚ) - 2 * ((C.covered (C.selectedMask output)).card : ℚ)

def accepts (C : Input) (q : ℚ) (output : List Bool) : Bool :=
  decide (C.comparisonCost output < q * C.m)

end MetricKMedian.Coverage.Input

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Constants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Filter

structure PartitionParameters (δ : ℝ) where
  D : ℕ
  t : ℕ
  ε : ℚ
  D_ge : 2 ≤ D
  t_pos : 1 ≤ t
  ε_pos : 0 < ε
  margin : 1 - (1 - 1 / (D : ℝ)) ^ D + (D : ℝ) / t +
    (t : ℝ)^2 * (D : ℝ)^2 * (ε : ℝ) < 1 - 1 / Real.exp 1 + δ

end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Encoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage

abbrev Raw := ℕ × ℕ × ℕ × List Bool

namespace Raw
abbrev m (r : Raw) := r.1
abbrev n (r : Raw) := r.2.1
abbrev k (r : Raw) := r.2.2.1
abbrev table (r : Raw) := r.2.2.2

end Raw

namespace Input

theorem n_pos (C : Input) : 0 < C.n := lt_of_lt_of_le C.k_pos C.k_le

end Input
end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Partition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage.Partitions
open Finset

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def hit (H : A → Finset B) : Finset (A → B) :=
  univ.filter (fun w => ∃ a, w a ∈ H a)

def avoid (H : A → Finset B) : Finset (A → B) :=
  univ.filter (fun w => ∀ a, w a ∉ H a)

@[simp] theorem mem_hit (H : A → Finset B) (w : A → B) :
    w ∈ hit H ↔ ∃ a, w a ∈ H a := by simp [hit]

@[simp] theorem mem_avoid (H : A → Finset B) (w : A → B) :
    w ∈ avoid H ↔ ∀ a, w a ∉ H a := by simp [avoid]

def avoidEquiv (H : A → Finset B) :
    {w : A → B // ∀ a, w a ∉ H a} ≃ ((a : A) → {b : B // b ∉ H a}) where
  toFun w a := ⟨w.val a,w.property a⟩
  invFun w := ⟨fun a => (w a).val,fun a => (w a).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def active (H : A → Finset B) : Finset A := univ.filter (fun a => (H a).Nonempty)

omit [Fintype B] [DecidableEq A] [DecidableEq B] in
@[simp] theorem mem_active (H : A → Finset B) (a : A) :
    a ∈ active H ↔ (H a).Nonempty := by simp [active]

end MetricKMedian.Coverage.Partitions

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Finset

structure ProjectionSystem (U V I A B : Type) where
  neighbor : V → I → U
  project : V → I → A → B

namespace ProjectionSystem
variable {U V I A B : Type} [Fintype U] [Fintype V] [Fintype I]
  [Fintype A] [Fintype B] [DecidableEq U] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B]
variable (G : ProjectionSystem U V I A B)

def labels (S : Finset (U × A)) (u : U) : Finset A :=
  univ.filter (fun a => (u,a) ∈ S)

omit [Fintype U] in
@[simp] theorem mem_labels (S : Finset (U × A)) (u : U) (a : A) :
    a ∈ labels S u ↔ (u,a) ∈ S := by simp [labels]

def parts (S : Finset (U × A)) (v : V) (b : B) : Finset I :=
  univ.filter (fun i => ∃ a ∈ labels S (G.neighbor v i), G.project v i a = b)

omit [Fintype U] [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq I] in
@[simp] theorem mem_parts (S : Finset (U × A)) (v : V) (b : B) (i : I) :
    i ∈ G.parts S v b ↔ ∃ a, (G.neighbor v i,a) ∈ S ∧ G.project v i a = b := by
  simp [parts]

def covered (S : Finset (U × A)) : Finset (V × (B → I)) :=
  univ.filter (fun p => ∃ i a, (G.neighbor p.1 i,a) ∈ S ∧ p.2 (G.project p.1 i a) = i)

omit [Fintype U] [DecidableEq V] in
@[simp] theorem mem_covered (S : Finset (U × A)) (v : V) (w : B → I) :
    (v,w) ∈ G.covered S ↔ w ∈ Partitions.hit (G.parts S v) := by
  simp only [covered, mem_filter, mem_univ, true_and, Partitions.mem_hit, mem_parts]
  constructor
  · rintro ⟨i,a,ha,hw⟩
    refine ⟨G.project v i a,a,?_,?_⟩
    · simpa only [hw] using ha
    · simp only [hw]
  · rintro ⟨b,a,ha,hb⟩
    exact ⟨w b,a,ha,by rw [hb]⟩

def LeftRegular (d : ℕ) : Prop :=
  ∀ u, (univ.filter (fun p : V × I => G.neighbor p.1 p.2 = u)).card = d

def bad (S : Finset (U × A)) : Finset V :=
  univ.filter (fun v => ∃ b, 1 < (G.parts S v b).card)

end ProjectionSystem
end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Lists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage.ProjectionSystem
open Finset

variable {U V I A B : Type} [Fintype U] [Fintype V] [Fintype I]
  [Fintype A] [Fintype B] [DecidableEq U] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B]
variable (G : ProjectionSystem U V I A B)

def DuplicateConsistent : Prop :=
  ∀ v i j, G.neighbor v i = G.neighbor v j → ∀ a, G.project v i a = G.project v j a

def agreement (left : U → A) : Finset V :=
  univ.filter (fun v => ∃ i j, i ≠ j ∧
    G.project v i (left (G.neighbor v i)) = G.project v j (left (G.neighbor v j)))

omit [Fintype U] [Fintype A] [Fintype B] [DecidableEq U] [DecidableEq V]
  [DecidableEq A] in
@[simp] theorem mem_agreement (left : U → A) (v : V) :
    v ∈ G.agreement left ↔ ∃ i j, i ≠ j ∧
    G.project v i (left (G.neighbor v i)) = G.project v j (left (G.neighbor v j)) := by
  simp [agreement]

def heavyHit (S : Finset (U × A)) (t : ℕ) : Finset V :=
  univ.filter (fun v => ∃ i, t < (labels S (G.neighbor v i)).card)

def lowBad (S : Finset (U × A)) (t : ℕ) : Finset V := G.bad S \ G.heavyHit S t

def cappedLabels (S : Finset (U × A)) (t : ℕ) (default : A) (u : U) : Finset A :=
  if (labels S u).card ≤ t ∧ (labels S u).Nonempty then labels S u else {default}

end MetricKMedian.Coverage.ProjectionSystem

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage.ProjectionSystem
open Finset

variable {U V I A B : Type} [Fintype U] [Fintype V] [Fintype I]
  [Fintype A] [Fintype B] [DecidableEq U] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B]
variable (G : ProjectionSystem U V I A B)

def sample (J : Type) : ProjectionSystem U (V × (J → I)) J A B where
  neighbor p j := G.neighbor p.1 (p.2 j)
  project p j a := G.project p.1 (p.2 j) a

variable (J : Type) [Fintype J] [DecidableEq J]

def satisfied (left : U → A) (right : V → B) : Finset (V × I) :=
  univ.filter (fun p => G.project p.1 p.2 (left (G.neighbor p.1 p.2)) = right p.1)

end MetricKMedian.Coverage.ProjectionSystem

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_ProjectionInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Finset

structure ProjectionInput (r a b : ℕ) where
  u : ℕ
  v : ℕ
  u_pos : 0 < u
  v_pos : 0 < v
  r_pos : 0 < r
  a_pos : 0 < a
  b_pos : 0 < b
  system : ProjectionSystem (Fin u) (Fin v) (Fin r) (Fin a) (Fin b)
  degree : ℕ
  regular : system.LeftRegular degree
  consistent : system.DuplicateConsistent

namespace ProjectionInput
variable {r a b : ℕ} (G : ProjectionInput r a b)

def Perfect : Prop := ∃ (left : Fin G.u → Fin a) (right : Fin G.v → Fin b), ∀ v i,
  G.system.project v i (left (G.system.neighbor v i)) = right v

def Sound (ε : ℝ) : Prop := ∀ left right,
  ((G.system.satisfied left right).card : ℝ) ≤ ε * G.v * r

abbrev Block (r b D : ℕ) := (Fin D → Fin r) × (Fin b → Fin D)
def width (r b D : ℕ) : ℕ := r^D * D^b

noncomputable def blockEquiv (r b D : ℕ) : Block r b D ≃ Fin (width r b D) :=
  (Fintype.equivFin _).trans (finCongr (by simp [Block,width]))

noncomputable def clientEquiv (D : ℕ) :
    ((Fin G.v × (Fin D → Fin r)) × (Fin b → Fin D)) ≃ Fin (G.v * width r b D) :=
  (Equiv.prodAssoc _ _ _).trans
    ((Equiv.prodCongr (Equiv.refl _) (blockEquiv r b D)).trans finProdFinEquiv)

abbrev facilityEquiv : (Fin G.u × Fin a) ≃ Fin (G.u * a) := finProdFinEquiv

noncomputable abbrev toCoverage (D : ℕ) (hD : 0 < D) : Input where
  m := G.v * width r b D
  n := G.u * a
  k := G.u
  m_pos := Nat.mul_pos G.v_pos (Nat.mul_pos (pow_pos G.r_pos _) (pow_pos hD _))
  k_pos := G.u_pos
  k_le := Nat.le_mul_of_pos_right _ G.a_pos
  incident x y :=
    let p := (G.clientEquiv D).symm x
    let q := G.facilityEquiv.symm y
    decide (∃ j : Fin D, G.system.neighbor p.1.1 (p.1.2 j) = q.1 ∧
      p.2 (G.system.project p.1.1 (p.1.2 j) q.2) = j)

@[simp] theorem incident_equiv (D : ℕ) (hD : 0 < D)
    (p : (Fin G.v × (Fin D → Fin r)) × (Fin b → Fin D))
    (q : Fin G.u × Fin a) :
    (G.toCoverage D hD).incident (G.clientEquiv D p) (G.facilityEquiv q) = true ↔
      ∃ j : Fin D, G.system.neighbor p.1.1 (p.1.2 j) = q.1 ∧
        p.2 (G.system.project p.1.1 (p.1.2 j) q.2) = j := by
  simp

end ProjectionInput
end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_ProjectionEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage

abbrev ProjectionRaw := List Bool × List (List (ℕ × List ℕ))
abbrev BlockCode := List ℕ × List ℕ

namespace ProjectionRaw

def lefts (R : ProjectionRaw) : List ℕ := List.range R.1.length
def rights (R : ProjectionRaw) : List ℕ := List.range R.2.length

def edge (R : ProjectionRaw) (v i : ℕ) : ℕ × List ℕ :=
  (((R.2[v]?).getD [])[i]?).getD (0,[])

def test (R : ProjectionRaw) (v : ℕ) (sw : BlockCode) (u a j : ℕ) : Bool :=
  let e := R.edge v ((sw.1[j]?).getD 0)
  decide (e.1 = u) && decide ((sw.2[(e.2[a]?).getD 0]?).getD 0 = j)

def incident (D : ℕ) (R : ProjectionRaw) (v : ℕ) (sw : BlockCode) (u a : ℕ) : Bool :=
  !((List.range D).filter (fun j => R.test v sw u a j)).isEmpty

end ProjectionRaw

namespace ProjectionInput
variable {r a b : ℕ} (G : ProjectionInput r a b)

theorem ofFn_product {α : Type} {m n : ℕ} (f : Fin (m*n) → α) :
    List.ofFn f = (List.finRange m).flatMap (fun i => (List.finRange n).map
      (fun j => f (finProdFinEquiv (i,j)))) := by
  rw [List.ofFn_mul,List.flatMap_def,← List.ofFn_eq_map]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rw [← List.ofFn_eq_map]
  apply congrArg List.ofFn
  funext j
  congr 1
  apply Fin.ext
  change i.val*n+j.val = j.val+n*i.val
  ring

end ProjectionInput
end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end


