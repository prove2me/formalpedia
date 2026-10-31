-- Prove2me | Definitions.Def_OAIQ053K019
-- name    : OAIQ053K019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:56:22.242979+00:00
-- url     : https://prove2.me/theorems/0395f2f9-d3f7-4d39-b2b6-7b4c8b08188f
-- title:
--   Definitions bundle OAIQ053K019 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 55 declarations of OpenAI's Lean: 17 definitions, 5 inductive types or structures and 33 theorems. The definitions and types are `OAI.MetricKMedian.FiniteLaw.sumMix`, `OAI.MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram.Input.raw`, `OAI.MetricKMedian.Gaussian.ListOperation.Rows`, `OAI.MetricKMedian.IntegerLaw.ListOperation.Input`, `OAI.MetricKMedian.IntegerLaw.ListOperation.Row`, `OAI.MetricKMedian.RationalBatchData.ProposalProgram.Input.enumActions`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.Input`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyGraphProgram.instLinearOrderSubtypeCopyFinMemFinset`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyList.activeOrder`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyList.orderEquiv`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyList.ordinal`, `OAI.MetricKMedian.RationalPhysicalKernel.HistoryProgram.nextCtx`, `OAI.MetricKMedian.RationalPhysicalKernel.RoundProgram.dummy`, `OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.Context`, `OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.Input`, `OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.Input.proposal`, `OAI.MetricKMedian.RationalPhysicalKernel.UpdateProgram.instLinearOrderSubtypeCopyFinMemFinset`, `OAI.MetricKMedian.RoundingHeight.denominator`, `OAI.MetricKMedian.RoundingProgram.Input`, `OAI.MetricKMedian.RoundingProgram.stateBound`, `OAI.MetricKMedian.SparseGraph.Program.QInput.raw`, `OAI.MetricKMedian.TaperGraphProgram.Input.raw`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Compression_AffineElimination`, `KMedian_Compression_AffineListOperations`, `KMedian_Compression_GaussianListOperations`, `KMedian_Compression_RationalScaling`, `KMedian_Geometry_NearestReindex`, `KMedian_Probability_SumLaws`, `KMedian_Process_BatchProposalProgram`, `KMedian_Process_CopyGraphProgram`, `KMedian_Process_CopyListEncoding`, `KMedian_Process_PhysicalBatchUpdateProgram`, `KMedian_Process_PhysicalHistoriesProgram`, `KMedian_Process_PhysicalRoundProgram`, `KMedian_Process_RoundCountsProgram`, `KMedian_Process_RoundingCoordinateHeight`, `KMedian_Process_RoundingListOperations`, `KMedian_Process_RoundingRunProgram`, `KMedian_Process_TaperGraphProgram`, `KMedian_Process_TaperReindex`, `KMedian_Programs_GraphLawProgram`, `KMedian_Programs_MaximumProgram`, `KMedian_Rounding_RationalWeightedInvariants`, `KMedian_Rounding_SignedGridInvariant`, `KMedian_Rounding_WeightedGridInvariant`, `KMedian_Sparse_SparseIterationHeight`.
--
--   **Imports.** It imports the bundles `OAIQ053K000`, `OAIQ053K001`, `OAIQ053K002`, `OAIQ053K003`, `OAIQ053K004`, `OAIQ053K005`, `OAIQ053K006` and `OAIQ053K007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K032`, `OAIQ053K033` and `OAIQ053K034`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K000
import Definitions.Def_OAIQ053K001
import Definitions.Def_OAIQ053K002
import Definitions.Def_OAIQ053K003
import Definitions.Def_OAIQ053K004
import Definitions.Def_OAIQ053K005
import Definitions.Def_OAIQ053K006
import Definitions.Def_OAIQ053K007

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_AffineElimination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian
open Finset

namespace IntegerLaw
variable {Ω I : Type} [Fintype Ω] [Fintype I]

theorem numerator_le (μ : IntegerLaw Ω) (i : Ω) : μ.numerator i ≤ μ.denominator := by
  rw [← μ.total]
  exact single_le_sum (fun j _ => μ.numerator_nonneg j) (mem_univ i)

end IntegerLaw
end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_RationalScaling
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
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Gaussian.ListOperation
open Finset
universe uα uβ
variable {α : Type uα} {β : Type uβ}

abbrev Rows := List Row

end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_AffineListOperations
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.IntegerLaw.ListOperation
open Binary Gaussian
open Finset
abbrev Row := Binary.IntegerList.Row

structure Input where
  n : ℕ
  d : ℕ
  μ : IntegerLaw (Fin n)
  v : Fin n → Fin d → ℤ
  large : d+1 < μ.support.card

end MetricKMedian.IntegerLaw.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingListOperations
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
attribute [-simp] _root_.OAI.MetricKMedian.SparseTargetSubset.point_initial _root_.OAI.MetricKMedian.SparseWeightedPartial.features_pair _root_.OAI.MetricKMedian.SparseWeightedPartial.features_single
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.RoundingList
open Binary Binary.Automatic Binary.Automatic.Poly RationalWeightedStep Finset

theorem fractional_list {n : ℕ} (p : Vector ℚ n) :
    fractional p.toList=((RationalWeightedStep.fractional p).sort).map Fin.val := by
  simp only [fractional,indices,Vector.length_toList,range_finRange,List.filter_map]
  unfold RationalWeightedStep.fractional
  rw [← EncodingLists.filter_range]
  apply congrArg (List.map Fin.val)
  apply List.filter_congr
  intro index _
  simp [frac, RationalWeightedStep.point]

theorem active_list {n : ℕ} (p : Vector ℚ n) :
    active p.toList=decide (1<(RationalWeightedStep.fractional p).card) := by
  simp only [active,fractional_list,List.length_map,Finset.length_sort]

theorem first_list {n : ℕ} (p : Vector ℚ n) (h : 1<(RationalWeightedStep.fractional p).card) :
    first p.toList=(RationalWeightedStep.pair p h).val.1.val := by
  unfold first indices
  rw [Vector.length_toList]
  apply findIdx_min
  · exact card_pos.mp (by omega)
  intro i
  simp [frac,RationalWeightedStep.fractional,RationalWeightedStep.point]

theorem second_list {n : ℕ} (p : Vector ℚ n) (h : 1<(RationalWeightedStep.fractional p).card) :
    second p.toList=(RationalWeightedStep.pair p h).val.2.val := by
  unfold second indices
  rw [Vector.length_toList,first_list p h]
  apply findIdx_min
  · rw [← card_pos,card_erase_of_mem (min'_mem _ _)]
    omega
  intro i
  simp only [frac,Vector.getElem?_toList,Vector.getElem?_eq_getElem i.isLt,Option.getD_some,
    ← Bool.decide_and,Finset.mem_erase]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]

  simp only [RationalWeightedStep.pair,Fin.val_ne_iff,RationalWeightedStep.fractional,mem_filter,mem_univ,true_and,point]
  exact and_comm

theorem get_point {n : ℕ} (p : Vector ℚ n) (i : Fin n) : p.toList[i.val]?.getD 0=point p i := by simp [point]
theorem up_list {n : ℕ} (p : Vector ℚ n) (i j : Fin n) (r : ℚ) :
    up p.toList i.val j.val r=RationalWeightedStep.up p i j r := by simp only [up,RationalWeightedStep.up,get_point]
theorem down_list {n : ℕ} (p : Vector ℚ n) (i j : Fin n) (r : ℚ) :
    down p.toList i.val j.val r=RationalWeightedStep.down p i j r := by simp only [down,RationalWeightedStep.down,get_point]
theorem move_list {n : ℕ} (p : Vector ℚ n) (i j : Fin n) (r t : ℚ) :
    move p.toList i.val j.val r t=(RationalWeightedStep.move p i j r t).toList := by
  simp only [move,indices,Vector.length_toList,range_finRange,List.map_map,RationalWeightedStep.move,Vector.toList_ofFn,List.ofFn_eq_map]
  congr 1
  funext k
  simp only [Function.comp_def,get_point,Fin.val_inj]

end MetricKMedian.RoundingList
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalWeightedInvariants
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalWeightedStep
open Finset
variable {n : ℕ}

theorem endpoint_weighted (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (b : Fin 2) :
    (∑ k, β k*point (endpoint β p b) k)=∑ k, β k*point p k := by
  by_cases h : 1 < (fractional p).card
  · let a := pair p h
    let r := β a.val.1/β a.val.2
    let t := if b=0 then up p a.val.1 a.val.2 r else -down p a.val.1 a.val.2 r
    have hb : (β a.val.2:ℝ) ≠ 0 := by exact_mod_cast (hβ a.val.2).ne'
    have hh := WeightedRounding.weighted_sum (fun k => (β k:ℝ)) (realPoint p)
      (i:=a.val.1) (j:=a.val.2) hb (t:ℝ)
    rw [← Rat.cast_div,← real_move] at hh
    simp only [realPoint] at hh
    simp only [endpoint,dite_eq_left h]
    exact_mod_cast hh
  · simp only [endpoint,dite_eq_right h]

end MetricKMedian.RationalWeightedStep
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_SumLaws
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.FiniteLaw
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

noncomputable def sumMix (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ) : FiniteLaw (Ω ⊕ Ξ) where
  weight := Sum.elim (fun ω => θ*μ.weight ω) (fun ξ => (1-θ)*ν.weight ξ)
  nonneg := by
    intro z
    cases z with
    | inl ω => exact mul_nonneg hθ0 (μ.nonneg ω)
    | inr ξ => exact mul_nonneg (sub_nonneg.mpr hθ1) (ν.nonneg ξ)
  total := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, ← Finset.mul_sum, μ.total, ν.total]
    ring

end MetricKMedian.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CopyListEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.RationalPhysicalKernel.CopyList
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row indices)
variable {f Δ : ℕ}
local instance instLinearOrderCopyFin_ra1c3ee_1 : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
abbrev activeOrder (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : LinearOrder ↥A :=
  @Subtype.instLinearOrder _ (copyOrder (F:=Fin f) (Δ:=Δ)) (·∈A)

 def ordinal (A : Finset (CopyState.Copy (F:=Fin f) Δ)) :=
  @Fintype.orderIsoFinOfCardEq A (activeOrder A) _ _ (Fintype.card_coe A)

end MetricKMedian.RationalPhysicalKernel.CopyList
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
 theorem least_map (e : α ≃o β) (U : Finset α) (d : α → ℚ) (hU : U.Nonempty) :
    least (U.map e.toEmbedding) (fun b => d (e.symm b)) (hU.map)=e (least U d hU) := by
  have him : (U.map e.toEmbedding).image (fun b => d (e.symm b))=U.image d := by
    ext q
    simp only [mem_image,mem_map]
    constructor
    · rintro ⟨b,⟨a,ha,rfl⟩,h⟩; exact ⟨a,ha,by simpa using h⟩
    · rintro ⟨a,ha,rfl⟩; exact ⟨e a,⟨a,ha,rfl⟩,by simp⟩
  unfold least
  have hf : (U.map e.toEmbedding).filter (fun b => d (e.symm b)=(U.image d).min' (hU.image _))=
      (U.filter (fun a => d a=(U.image d).min' (hU.image _))).map e.toEmbedding := by
    ext b
    simp only [mem_filter,mem_map]
    constructor
    · rintro ⟨⟨a,ha,rfl⟩,hh⟩; exact ⟨a,⟨ha,by simpa using hh⟩,rfl⟩
    · rintro ⟨a,⟨ha,hh⟩,rfl⟩; exact ⟨⟨a,ha,rfl⟩,by simpa using hh⟩
  simp only [him]
  simp only [hf]
  exact min_map e _ _

 theorem takeNearest_map (e : α ≃o β) (d : α → ℚ) (t : ℕ) (U : Finset α) :
    takeNearest (fun b => d (e.symm b)) t (U.map e.toEmbedding)=(takeNearest d t U).map e.toEmbedding := by
  induction t generalizing U with
  | zero => simp only [takeNearest,map_empty]
  | succ t ih =>
    by_cases hU : U.Nonempty
    · rw [takeNearest,takeNearest,dite_eq_left hU,dite_eq_left (hU.map),least_map e U d hU]
      have he : (U.map e.toEmbedding).erase (e (least U d hU))=(U.erase (least U d hU)).map e.toEmbedding := by
        exact (map_erase e.toEmbedding U (least U d hU)).symm
      rw [he,ih,map_insert]
      rfl
    · have he := not_nonempty_iff_eq_empty.mp hU
      subst U
      simp [takeNearest]
end MetricKMedian.Preparation.RationalNearest

namespace MetricKMedian.RationalPhysicalKernel.CopyList
open CopyState
variable {f Δ : ℕ}

local instance instLinearOrderCopyFin_1_ra1c3ee_1 : LinearOrder (Copy (F:=Fin f) Δ) := copyOrder
def orderEquiv : @OrderIso (Copy (F:=Fin f) Δ) (Fin (f*Δ)) (copyOrder (F:=Fin f) (Δ:=Δ)).toLE inferInstance where
  toEquiv := finProdFinEquiv
  map_rel_iff' := @StrictMono.le_iff_le _ _ (copyOrder (F:=Fin f) (Δ:=Δ)) _ _ rank_strictMono
end MetricKMedian.RationalPhysicalKernel.CopyList
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseIterationHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section

namespace MetricKMedian.SparseWeightedPartial
open Binary RationalWeightedStep
variable {n : ℕ}
theorem features_height (p : Vector ℚ n) (L : ℕ) (hp : ∀ i, HasHeight (point p i) L)
    (a : Fin (n+n*n)) : HasHeight (features p a) (2*L) := by
  unfold features
  generalize finSumFinEquiv.symm a=z
  cases z with
  | inl i => exact (hp i).mono (by omega)
  | inr ij => simpa only [Sum.elim_inr,← two_mul] using (hp (finProdFinEquiv.symm ij).1).mul (hp (finProdFinEquiv.symm ij).2)
end MetricKMedian.SparseWeightedPartial

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
open Finset FixedBatch Binary Binary.PolyProgram
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row )
variable {C : Type} (I : C → Type) [∀ c, LinearOrder (I c)] [∀ c, Fintype (I c)]

variable {I}

def Input.enumActions (x : Input I) := enumeration (graph x.G) (heavySet (graphMass x.G x.g) x.b)
end MetricKMedian.RationalBatchData.ProposalProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_WeightedGridInvariant
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
attribute [-simp] _root_.OAI.MetricKMedian.SparseTargetSubset.point_initial _root_.OAI.MetricKMedian.SparseWeightedPartial.features_pair _root_.OAI.MetricKMedian.SparseWeightedPartial.features_single
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section

namespace MetricKMedian.RationalWeightedStep
open Finset RationalGrid
variable {n : ℕ}

theorem point_move_self (p : Vector ℚ n) (i j : Fin n) (hij : i≠j) (r t : ℚ) :
    point (move p i j r t) i=point p i+t := by
  simp [point,move,hij]
theorem point_move_other (p : Vector ℚ n) (i j : Fin n) (hij : i≠j) (r t : ℚ) :
    point (move p i j r t) j=point p j-t*r := by
  simp [point,move,Ne.symm hij,sub_eq_add_neg]
theorem point_move_rest (p : Vector ℚ n) (i j k : Fin n) (hki : k≠i) (hkj : k≠j) (r t : ℚ) :
    point (move p i j r t) k=point p k := by
  simp [point,move,hki,hkj]

theorem move_pair_weighted (β : Fin n → ℚ) (p : Vector ℚ n) (i j : Fin n)
    (hij : i≠j) (hj : β j ≠ 0) (t : ℚ) :
    β i*point (move p i j (β i/β j) t) i+
      β j*point (move p i j (β i/β j) t) j=β i*point p i+β j*point p j := by
  rw [point_move_self _ _ _ hij,point_move_other _ _ _ hij]
  field_simp
  ring

theorem up_integral (p : Vector ℚ n) (i j : Fin n) (hij : i≠j) (r : ℚ) (hr : r≠0) :
    point (move p i j r (up p i j r)) i=1 ∨ point (move p i j r (up p i j r)) j=0 := by
  rw [point_move_self _ _ _ hij,point_move_other _ _ _ hij]
  unfold up
  rcases le_total (1-point p i) (point p j/r) with h | h
  · left; rw [min_eq_left h]; ring
  · right; rw [min_eq_right h,div_mul_cancel₀ _ hr,sub_self]

theorem down_integral (p : Vector ℚ n) (i j : Fin n) (hij : i≠j) (r : ℚ) (hr : r≠0) :
    point (move p i j r (-down p i j r)) i=0 ∨ point (move p i j r (-down p i j r)) j=1 := by
  rw [point_move_self _ _ _ hij,point_move_other _ _ _ hij]
  unfold down
  rcases le_total (point p i) ((1-point p j)/r) with h | h
  · left; rw [min_eq_left h]; ring
  · right; rw [min_eq_right h,neg_mul,div_mul_cancel₀ _ hr]; ring

theorem endpoint_grid (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (D : ℤ) (hb : ∀ i, At D (β i)) (p : Vector ℚ n)
    (hp : ∀ i, At D (β i*point p i)) (b : Fin 2) :
    ∀ i, At D (β i*point (endpoint β p b) i) := by
  by_cases h : 1 < (fractional p).card
  · let a := pair p h
    let i := a.val.1
    let j := a.val.2
    let r := β i/β j
    let t := if b=0 then up p i j r else -down p i j r
    let q := move p i j r t
    have hij : i≠j := a.property.2.2
    have hr : r≠0 := (div_pos (hβ i) (hβ j)).ne'
    have he : endpoint β p b=q := by rw [endpoint,dite_eq_left h]
    have hw : β i*point q i+β j*point q j=β i*point p i+β j*point p j :=
      move_pair_weighted β p i j hij (hβ j).ne' t
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
        convert hh using 1; linarith
      · have haj : At D (β j*point q j) := by
          rcases hj with hj | hj
          · rw [hj,mul_zero]; exact RationalGrid.zero _
          · rw [hj,mul_one]; exact hb j
        refine ⟨?_,haj⟩
        have hh := RationalGrid.sub (RationalGrid.add (hp i) (hp j)) haj
        convert hh using 1; linarith
    intro k
    rw [he]
    by_cases hki : k=i
    · subst k; exact hpi.1
    by_cases hkj : k=j
    · subst k; exact hpi.2
    simpa only [q,point_move_rest _ _ _ _ hki hkj] using hp k
  · simpa only [endpoint,dite_eq_right h] using hp

end MetricKMedian.RationalWeightedStep
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_SignedGridInvariant
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
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
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingCoordinateHeight
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.RationalGrid
open Binary

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
-- module Solutions.OAIQ053_KM.KMedian_Process_RoundingRunProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.RoundingProgram
open Binary Binary.PolyProgram Function Polynomial
open SparseIntegerLaw.BinarySparse

structure Input (signed : Bool) where
  n : ℕ
  β : Fin n → ℚ
  p : Vector ℚ n
  positive : signed=false → ∀ i, 0<β i
  feasible : ∀ i, 0 ≤ RationalWeightedStep.point p i ∧ RationalWeightedStep.point p i ≤ 1

def stateBound (L : ℕ) :=
  2*L+1+ (2*(2*(heightBound L+4)+1+supportBound L*(2*(heightBound L+4)+1))+1+
    supportBound L*(2*(L*(2*(3*coordinateBound L+10)+1))+1))

theorem statePolynomial_eval (L : ℕ) : statePolynomial.eval L=stateBound L := by
  simp only [statePolynomial,stateBound,heightBound,coordinateBound,supportBound,CPoly,NPoly,HPoly,
    RoundingHeight.stepHeight,SparseIntegerLaw.stepHeight,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]

end MetricKMedian.RoundingProgram
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
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse

def QInput.raw (x : QInput) : List Unit × List (List ℚ) :=
  (List.replicate x.n (),List.ofFn fun i => List.ofFn fun h => x.q h i)
end MetricKMedian.SparseGraph.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_TaperGraphProgram
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
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
end MetricKMedian.TaperGraphProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_TaperReindex
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                    
section
namespace MetricKMedian.Taper
open Finset
variable {I J : Type} [Fintype I] [Fintype J]

 theorem upper_reindex (e : I ≃ J) (d : J → ℚ) : upper (fun i => d (e i))=upper d := by
  exact congrArg (fun q : ℚ => 1+q) (e.sum_comp (fun j => (d j)⁻¹))
 theorem breaks_reindex (e : I ≃ J) (P : ℚ) (d : J → ℚ) :
    breakpoints P (fun i => d (e i))=breakpoints P d := by
  unfold breakpoints
  rw [upper_reindex,image_univ_reindex e (fun j => (1-P)/d j),image_univ_reindex e (fun j => 1/d j)]
 theorem colocated_reindex (e : I ≃ J) (g : ℚ) (d : J → ℚ) :
    rationalColocatedMass g (fun i => d (e i))=rationalColocatedMass g d :=
  e.sum_comp (fun j => if d j=0 then g else 0)

variable [LinearOrder I] [LinearOrder J]
omit [LinearOrder I] [LinearOrder J] in
 theorem zeros_reindex (e : I ≃ J) (d : J → ℚ) :
    (zeroSources (fun i => d (e i))).map e.toEmbedding=zeroSources d := by
  ext j
  simp only [mem_map_equiv,zeroSources,mem_filter,mem_univ,true_and,e.apply_symm_apply]
omit [Fintype I] [Fintype J] in
 theorem extend_reindex (e : I ≃o J) (own Z : Finset I) (Δ : ℕ) :
    extend (own.map e.toEquiv.toEmbedding) (Z.map e.toEquiv.toEmbedding) Δ=
      (extend own Z Δ).map e.toEquiv.toEmbedding := by
  have hs : ((Z\own).map e.toEquiv.toEmbedding).sort=
      ((Z\own).sort).map e := by
    exact (Finset.map_sort e.toEquiv.toEmbedding (Z\own) (·≤·) (·≤·)
      (fun _ _ _ _ => e.le_iff_le.symm)).symm
  have hm (xs : List I) : (xs.map e).toFinset=xs.toFinset.map e.toEquiv.toEmbedding := by
    ext j; simp only [List.mem_toFinset,List.mem_map,mem_map,Equiv.toEmbedding_apply]
    rfl
  simp only [extend,← Finset.map_sdiff,card_map,hs,← List.map_take,hm,Finset.map_union]
 theorem zeroMarginal_reindex (e : I ≃o J) (d : J → ℚ) (own : Finset I) (Δ : ℕ) (i : I) :
    zeroMarginal d (own.map e.toEquiv.toEmbedding) Δ (e i)=
      zeroMarginal (fun j => d (e j)) own Δ i := by
  rw [zeroMarginal,zeroSelection,← zeros_reindex e.toEquiv,extend_reindex]
  simp only [mem_map_equiv,zeroMarginal,zeroSelection]
  change (if e.toEquiv.symm (e.toEquiv i)∈extend own (zeroSources (fun j => d (e j))) Δ then (1:ℚ) else 0)=_
  rw [e.toEquiv.symm_apply_apply]
  rfl
end MetricKMedian.Taper
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CopyGraphProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
namespace MetricKMedian.RationalPhysicalKernel.CopyGraphProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row )
open CopyList

structure Input where
  f : ℕ
  Δ : ℕ
  d : Fin f → Fin f → ℚ
  g : ℚ
  P : ℚ
  positive : 0<P
  A : Finset (CopyState.Copy (F:=Fin f) Δ)

local instance instLinearOrderCopyFin_ra1c3ee_2 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
local instance instLinearOrderSubtypeCopyFinMemFinset {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : LinearOrder ↥A := activeOrder A

end MetricKMedian.RationalPhysicalKernel.CopyGraphProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalBatchUpdateProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                  
section
namespace MetricKMedian.RationalPhysicalKernel.UpdateProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset FixedBatch
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row )
open CopyList
local instance instLinearOrderCopyFin_ra1c3ee_3 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
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
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalRoundProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.RationalPhysicalKernel.RoundProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row )
open CopyList UpdateProgram

local instance instLinearOrderCopyFin_ra1c3ee_4 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
local instance instLinearOrderSubtypeCopyFinMemFinset_ra1c3ee_1 {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : LinearOrder ↥A := activeOrder A
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
-- module Solutions.OAIQ053_KM.KMedian_Process_PhysicalHistoriesProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.RationalPhysicalKernel.HistoryProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row )
open CopyList UpdateProgram

local instance instLinearOrderCopyFin_ra1c3ee_5 {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
local instance instLinearOrderSubtypeCopyFinMemFinset_ra1c3ee_2 {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : LinearOrder ↥A := activeOrder A
def nextCtx (x : Context) (P : ℚ) (hP : 0<P) (A : Finset (CopyState.Copy (F:=Fin x.f) x.Δ)) : Context :=
  {x with toInput := {x.toInput with P:=P,positive:=hP,A:=A}}

end MetricKMedian.RationalPhysicalKernel.HistoryProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_MaximumProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.MaskProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row )
 theorem maximum_eq_finset (xs : List ℚ) (U : Finset ℚ) (hU : U.Nonempty)
    (hm : ∀ q, q∈xs ↔ q∈U) : maximum xs=U.max' hU := by
  have hne : xs≠[] := by
    intro he
    obtain ⟨q,hq⟩ := hU
    have hx := (hm q).mpr hq
    rw [he] at hx
    cases hx
  have hd : xs.head?.getD 0∈xs := by
    cases xs with
    | nil => contradiction
    | cons a xs => exact List.mem_cons_self
  apply LPBinary.foldl_max_eq
  · exact le_max' U _ ((hm _).mp hd)
  · exact (hm _).mpr (max'_mem U hU)
  · intro q hq
    exact le_max' U q ((hm q).mp hq)
end MetricKMedian.MaskProgram
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
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row )
open RationalPhysicalKernel CopyList
variable {τ : ℝ}
def Input.raw (x : Input) : Raw := (List.replicate x.f (),((List.ofFn (fun i => List.ofFn (x.d₀ i)),
  List.ofFn (fun c => List.ofFn (x.d c))),List.ofFn x.n))
end MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram
end

end OAI
end


