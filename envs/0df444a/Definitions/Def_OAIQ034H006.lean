-- Prove2me | Definitions.Def_OAIQ034H006
-- name    : OAIQ034H006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T05:36:44.098392+00:00
-- url     : https://prove2.me/theorems/42ef72fd-04d0-4c52-8091-8c1cc4e375fa
-- title:
--   Definitions bundle OAIQ034H006 of the split of OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HyperbolicObstruction.main`, carved from OpenAI's openai/math development (OpenAI, *A hyperbolic group with no geometric CAT(0) action (result family 257)*, OpenAI Math Release, September 25, 2026, result family 257, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 269 declarations of OpenAI's Lean: 80 definitions, 5 inductive types or structures, 12 instances and 172 theorems. The definitions and types are `OAI.HyperbolicObstruction.FinitePolyhedron.EdgeChain.steps`, `OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.EdgeData`, `OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.edgeParameter`, `OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.liftedClosedFace`, `OAI.HyperbolicObstruction.GeometricAction.pullback`, `OAI.HyperbolicObstruction.IncidenceTemplate.Admissible`, `OAI.HyperbolicObstruction.IncidenceTemplate.ConditionalData`, `OAI.HyperbolicObstruction.IncidenceTemplate.ConditionalData.test`, `OAI.HyperbolicObstruction.IncidenceTemplate.ConditionalTest`, `OAI.HyperbolicObstruction.IncidenceTemplate.CoreAdmissible`, `OAI.HyperbolicObstruction.IncidenceTemplate.actualProbability`, `OAI.HyperbolicObstruction.IncidenceTemplate.actualRowCost`, `OAI.HyperbolicObstruction.IncidenceTemplate.coreExponent`, `OAI.HyperbolicObstruction.IncidenceTemplate.criticalExponent`, `OAI.HyperbolicObstruction.IncidenceTemplate.errorRate`, `OAI.HyperbolicObstruction.IncidenceTemplate.extensionRate`, `OAI.HyperbolicObstruction.IncidenceTemplate.fanCount`, `OAI.HyperbolicObstruction.IncidenceTemplate.fanScore`, `OAI.HyperbolicObstruction.IncidenceTemplate.freshCount`, `OAI.HyperbolicObstruction.IncidenceTemplate.freshFields`, `OAI.HyperbolicObstruction.IncidenceTemplate.freshScore`, `OAI.HyperbolicObstruction.IncidenceTemplate.leafRate`, `OAI.HyperbolicObstruction.IncidenceTemplate.looseCount`, `OAI.HyperbolicObstruction.IncidenceTemplate.pattern`, `OAI.HyperbolicObstruction.IncidenceTemplate.rowCost`, `OAI.HyperbolicObstruction.IncidenceTemplate.rowSurcharge`, `OAI.HyperbolicObstruction.IncidenceTemplate.singletonData`, `OAI.HyperbolicObstruction.IndexedFilling.boundary`, `OAI.HyperbolicObstruction.IndexedFilling.cellBoundary`, `OAI.HyperbolicObstruction.LocalGeodesic.Deck`, `OAI.HyperbolicObstruction.LocalGeodesic.basedHomeomorph`, `OAI.HyperbolicObstruction.LocalGeodesic.basedLift`, `OAI.HyperbolicObstruction.LocalGeodesic.deckGeometricAction`, `OAI.HyperbolicObstruction.LocalGeodesic.deckIsometricAction`, `OAI.HyperbolicObstruction.LocalGeodesic.deckIsometry`, `OAI.HyperbolicObstruction.LocalGeodesic.deckPiOneEquiv`, `OAI.HyperbolicObstruction.LocalGeodesic.deckSubgroup`, `OAI.HyperbolicObstruction.LocalGeodesic.developedSegment`, `OAI.HyperbolicObstruction.LocalGeodesic.intrinsicDist`, `OAI.HyperbolicObstruction.LocalGeodesic.intrinsicMetric` and 45 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/HyperbolicGroups, in whole or in part: `HyperbolicGroups_Cost`, `HyperbolicGroups_DevelopmentDeck`, `HyperbolicGroups_DevelopmentGeodesic`, `HyperbolicGroups_DevelopmentGeometricAction`, `HyperbolicGroups_DevelopmentProper`, `HyperbolicGroups_DevelopmentRadial`, `HyperbolicGroups_Deviation`, `HyperbolicGroups_EdgeCoordinates`, `HyperbolicGroups_Exceptional`, `HyperbolicGroups_ExtensionConditioning`, `HyperbolicGroups_ExtensionMargin`, `HyperbolicGroups_FinitePolygonModel`, `HyperbolicGroups_FiniteSampling`, `HyperbolicGroups_Graph`, `HyperbolicGroups_GraphAction`, `HyperbolicGroups_IncidenceTemplate`, `HyperbolicGroups_IndexedFillingValue`, `HyperbolicGroups_IndexedPictureClosed`, `HyperbolicGroups_IndexedPictureExistence`, `HyperbolicGroups_IndexedWordPicture`, `HyperbolicGroups_LeafFiber`, `HyperbolicGroups_LocalGeodesicCover`, `HyperbolicGroups_LocalGeodesicDistance`, `HyperbolicGroups_LocalGeodesicLength`, `HyperbolicGroups_LocalGeodesicRebase`, `HyperbolicGroups_LocalGeodesicTopology`, `HyperbolicGroups_LocalSegmentContinuation`, `HyperbolicGroups_LocalSegmentTools`, `HyperbolicGroups_LoopSpaceReversal`, `HyperbolicGroups_MetricHexagon`, `HyperbolicGroups_MetricProduct`, `HyperbolicGroups_Moment`, `HyperbolicGroups_Pinned`, `HyperbolicGroups_Random`, `HyperbolicGroups_ShortSegmentLift`, `HyperbolicGroups_SixCounts`, `HyperbolicGroups_SmallSimplexCoordinates`, `HyperbolicGroups_StarActual`, `HyperbolicGroups_StarCoupling`, `HyperbolicGroups_StarError`, `HyperbolicGroups_StarFiber`, `HyperbolicGroups_StarMean`, `HyperbolicGroups_StarModel`, `HyperbolicGroups_StarRate`, `HyperbolicGroups_StarVariance`, `HyperbolicGroups_StationaryInterpolation`, `HyperbolicGroups_TableSelection`, `HyperbolicGroups_Template`, `HyperbolicGroups_Test`, `HyperbolicGroups_TriangleSquare`, `HyperbolicGroups_TriangleSquareFurther`, `HyperbolicGroups_VoltageClosedCells`, `HyperbolicGroups_VoltageEdgeAgreement`, `HyperbolicGroups_VoltagePrismGluing`, `HyperbolicGroups_WalkClasses`.
--
--   **Imports.** It imports the published bundle `Def_HyperbolicObstruction`; the bundles `OAIQ034H000`, `OAIQ034H001` and `OAIQ034H002` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ034H010`; the proof of `OAI.HyperbolicObstruction.main`.
-- source:
--   OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 257; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-hyperbolic-group-with-no-geometric-CAT0-action-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/HyperbolicGroups at commit adc7f12

import Mathlib
import Definitions.Def_HyperbolicObstruction
import Definitions.Def_OAIQ034H000
import Definitions.Def_OAIQ034H001
import Definitions.Def_OAIQ034H002

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MetricHexagon
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section


noncomputable section


noncomputable section

noncomputable section


noncomputable section
open scoped BigOperators ENNReal
namespace HyperbolicObstruction
namespace MetricScale
universe u

variable {r : ℝ} {hr : 0 < r} {X : Type u} [MetricSpace X]

variable (h : CATZero X)
include h

theorem catZero : CATZero (Space r hr X) := by
  intro x y
  refine ⟨fun t => ⟨CATZero.segment h x.val y.val t⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · apply Space.ext
    exact (CATZero.segment_spec h _ _).1
  · apply Space.ext
    exact (CATZero.segment_spec h _ _).2.1
  · intro s hs t ht
    change r * dist (CATZero.segment h x.val y.val s) (CATZero.segment h x.val y.val t) =
      |s - t| * (r * dist x.val y.val)
    rw [CATZero.segment_dist h _ _ hs ht]
    ring
  · intro z t ht
    have hi := mul_le_mul_of_nonneg_left (CATZero.segment_cn h x.val y.val z.val ht)
      (sq_nonneg r)
    simp only [dist_eq]
    nlinarith only [hi]

end MetricScale


end HyperbolicObstruction
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Template
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace IncidenceTemplate
open scoped BigOperators

lemma card_fan : ∀ i : Fin 7, (fan i).card = ![6,6,6,4,3,3,3] i := by decide

lemma card_twoPaths : Fintype.card TwoPath = 90 := by decide


/-- The fan membership partition includes the unique loose edge separately. -/
lemma partition_per_edge : ∀ e : Edge,
    (if isLoose e then 1 else 0) + (∑ i, if e ∈ fan i then 1 else 0) = (1 : ℕ) := by
  decide

def fanCount (W : Finset Edge) (i : Fin 7) : ℕ := (W ∩ fan i).card

def looseCount (W : Finset Edge) : ℕ := (W.filter isLoose).card

lemma count_partition (W : Finset Edge) :
    W.card = looseCount W + ∑ i, fanCount W i := by
  classical
  calc
    W.card = ∑ e ∈ W, (1 : ℕ) := by simp
    _ = ∑ e ∈ W, ((if isLoose e then 1 else 0) +
        ∑ i, if e ∈ fan i then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro e _
      exact (partition_per_edge e).symm
    _ = looseCount W + ∑ i, fanCount W i := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      congr 1
      · simp [looseCount]
      · apply Finset.sum_congr rfl
        intro i _
        simp [fanCount]

lemma fanCount_le (W : Finset Edge) (i : Fin 7) : fanCount W i ≤ (fan i).card :=
  Finset.card_le_card Finset.inter_subset_right

lemma fanCount_eq_iff (W : Finset Edge) (i : Fin 7) :
    fanCount W i = (fan i).card ↔ fan i ⊆ W := by
  unfold fanCount
  constructor
  · intro hc
    have he := Finset.eq_of_subset_of_card_le Finset.inter_subset_right hc.ge
    exact Finset.inter_eq_right.mp he
  · intro hs
    rw [Finset.inter_eq_right.mpr hs]

lemma fan_card_lower (i : Fin 7) : 3 ≤ (fan i).card := by
  rw [card_fan]
  fin_cases i <;> decide

/-- Each fan retains two units of critical exponent even when fully charged. -/
def fanScore (W : Finset Edge) (i : Fin 7) : ℤ :=
  fanCount W i - if fan i ⊆ W then ((fan i).card : ℤ) - 2 else 0

lemma fanScore_lower (W : Finset Edge) (i : Fin 7) :
    (min (fanCount W i) 2 : ℕ) ≤ fanScore W i := by
  have ha := fanCount_le W i
  have hk := fan_card_lower i
  unfold fanScore
  by_cases h : fan i ⊆ W
  · have he := (fanCount_eq_iff W i).mpr h
    simp only [h, ite_true]
    omega
  · simp only [h, ite_false, sub_zero]
    exact_mod_cast min_le_left (fanCount W i) 2

def coreExponent (W : Finset Edge) : ℤ :=
  W.card - (∑ i, if fan i ⊆ W then ((fan i).card : ℤ) - 2 else 0) -
    if W = Finset.univ then 12 else 0

lemma coreExponent_decompose (W : Finset Edge) :
    coreExponent W = looseCount W + ∑ i, fanScore W i -
      if W = Finset.univ then 12 else 0 := by
  unfold coreExponent fanScore
  rw [count_partition W, Nat.cast_add, Nat.cast_sum, Finset.sum_sub_distrib]
  ring

lemma coreExponent_univ : coreExponent Finset.univ = 3 := by
  decide

lemma coreExponent_lower (W : Finset Edge) :
    (min W.card 2 : ℕ) ≤ coreExponent W := by
  by_cases h : W = Finset.univ
  · subst W
    rw [coreExponent_univ]
    have hmin := min_le_right (Finset.univ : Finset Edge).card 2
    omega
  · rw [coreExponent_decompose, ite_eq_right h, sub_zero]
    have hs : (∑ i, (min (fanCount W i) 2 : ℕ) : ℤ) ≤ ∑ i, fanScore W i :=
      Finset.sum_le_sum (fun i _ => fanScore_lower W i)
    have hs' := min_sum_le_sum_min Finset.univ (fanCount W)
    have hw := count_partition W
    have hm : min W.card 2 ≤ looseCount W + ∑ i, min (fanCount W i) 2 := by omega
    have hc : ((min W.card 2 : ℕ) : ℤ) ≤ (looseCount W : ℤ) +
        ((∑ i, min (fanCount W i) 2 : ℕ) : ℤ) := by exact_mod_cast hm
    rw [Nat.cast_sum] at hc
    linarith

/-- Admissibility of core-field sets, retaining the exact three/two quotas. -/
def CoreAdmissible (S : Finset Edge) : Prop :=
  S.card ≤ 3 ∧ ∀ i, fanCount S i ≤ 2

lemma coreExponent_admissible (S W : Finset Edge) (hS : CoreAdmissible S)
    (hSW : S ⊆ W) : (S.card : ℤ) ≤ coreExponent W := by
  by_cases h : W = Finset.univ
  · subst W
    rw [coreExponent_univ]
    exact_mod_cast hS.1
  · rw [coreExponent_decompose, ite_eq_right h, sub_zero, count_partition S,
      Nat.cast_add, Nat.cast_sum]
    apply add_le_add
    · exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hSW)
    · apply Finset.sum_le_sum
      intro i _
      have hm : fanCount S i ≤ fanCount W i :=
        Finset.card_le_card (Finset.inter_subset_inter_right hSW)
      have ha := hS.2 i
      have hmin : fanCount S i ≤ min (fanCount W i) 2 := le_min hm ha
      exact (by exact_mod_cast hmin : (fanCount S i : ℤ) ≤
        (min (fanCount W i) 2 : ℕ)).trans (fanScore_lower W i)


def freshFields (W : Finset Field) (τ : TwoPath) : Finset (Fin 2) :=
  Finset.univ.filter (fun j : Fin 2 => (Sum.inr (τ, j) : Field) ∈ W)

def freshCount (W : Finset Field) (τ : TwoPath) : ℕ := (freshFields W τ).card

lemma freshCount_eq_two_iff (W : Finset Field) (τ : TwoPath) :
    freshCount W τ = 2 ↔ ∀ j : Fin 2, Sum.inr (τ, j) ∈ W := by
  classical
  simpa only [freshCount, freshFields, Finset.card_univ, Fintype.card_fin,
    Finset.mem_univ, forall_const] using
    (Finset.card_filter_eq_iff (s := (Finset.univ : Finset (Fin 2)))
      (p := fun j => (Sum.inr (τ, j) : Field) ∈ W))

lemma count_split (W : Finset Field) :
    W.card = W.toLeft.card + ∑ τ, freshCount W τ := by
  have hc := card_sum_prod (E := Edge) (T := TwoPath) (J := Fin 2) W
  exact hc

def freshScore (W : Finset Field) (τ : TwoPath) : ℤ :=
  freshCount W τ - if squareSupport τ ⊆ W then 2 else 0

lemma freshScore_nonneg (W : Finset Field) (τ : TwoPath) : 0 ≤ freshScore W τ := by
  unfold freshScore
  by_cases h : squareSupport τ ⊆ W
  · have hc : freshCount W τ = 2 := by
      rw [freshCount_eq_two_iff]
      intro j
      apply h
      fin_cases j <;> simp [squareSupport]
    simp [h, hc]
  · simp [h]

def criticalExponent (W : Finset Field) : ℤ :=
  coreExponent W.toLeft + ∑ τ, freshScore W τ

/-- Exact admissibility from Definition 2.3 of the manuscript. -/
def Admissible (S : Finset Field) : Prop :=
  (S.toRight = ∅ ∧ CoreAdmissible S.toLeft) ∨
    ∃ τ : TwoPath, S ⊆ squareSupport τ ∧ S.card ≤ 2

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IncidenceTemplate
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace HyperbolicObstruction

namespace IncidenceTemplate

instance instRowDecidableEq : DecidableEq Row := instDecidableEqSum

def rowCost : Row → ℤ
  | Sum.inl i => (fan i).card - 2
  | Sum.inr (Sum.inl _) => 12
  | Sum.inr (Sum.inr _) => 2

def pattern : SparsePattern.Pattern Field Row where
  support := rowSupport
  cost := rowCost
  nonneg r := by
    rcases r with i | (_ | τ)
    · have h := fan_card_lower i
      dsimp [rowCost]
      omega
    · norm_num [rowCost]
    · norm_num [rowCost]

lemma pattern_exponent (W : Finset Field) :
    pattern.exponent W = criticalExponent W := by
  classical
  change (W.card : ℤ) - (∑ r, if rowSupport r ⊆ W then rowCost r else 0) = _
  simp only [Fintype.sum_sum_type, Fintype.sum_unique]
  dsimp only [rowSupport, rowCost]
  simp only [Finset.map_inl_subset_iff_subset_toLeft, Finset.univ_subset_iff]
  rw [count_split, Nat.cast_add, Nat.cast_sum]
  unfold criticalExponent coreExponent freshScore
  rw [Finset.sum_sub_distrib]
  ring_nf
  rfl

lemma admissible_card (S : Finset Field) (hS : Admissible S) : S.card ≤ 3 := by
  rcases hS with ⟨he, hc⟩ | ⟨τ, _, hc⟩
  · have hh := Finset.card_toLeft_add_card_toRight (u := S)
    rw [he, Finset.card_empty, add_zero] at hh
    exact hh ▸ hc.1
  · omega

lemma admissible_subset {S T : Finset Field} (hT : Admissible T)
    (hST : S ⊆ T) : Admissible S := by
  rcases hT with ⟨ht, hc, hf⟩ | ⟨τ, hs, hc⟩
  · left
    refine ⟨?_, (Finset.card_le_card (Finset.toLeft_subset_toLeft hST)).trans hc, ?_⟩
    · exact Finset.subset_empty.mp (ht ▸ Finset.toRight_subset_toRight hST)
    · intro i
      exact (Finset.card_le_card (Finset.inter_subset_inter_right
        (Finset.toLeft_subset_toLeft hST))).trans (hf i)
  · exact Or.inr ⟨τ, hST.trans hs, (Finset.card_le_card hST).trans hc⟩

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Cost
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction

namespace IncidenceTemplate
/-- Exact increases from critical to actual array-entry costs. -/
def rowSurcharge (α β δ : ℝ) : Row → ℝ
  | Sum.inl _ => α
  | Sum.inr (Sum.inl _) => β - 7 * α
  | Sum.inr (Sum.inr _) => δ

/-- Source Equation (sample:eq-costs), with the critical integer cost displayed. -/
def actualRowCost (α β δ : ℝ) (r : Row) : ℝ := rowCost r + rowSurcharge α β δ r

lemma rowSurcharge_nonneg {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7 * α ≤ β) (hd : 0 ≤ δ)
    (r : Row) : 0 ≤ rowSurcharge α β δ r := by
  rcases r with i | (_ | τ)
  · exact ha
  · exact sub_nonneg.mpr hb
  · exact hd

lemma rowSurcharge_sum (α β δ : ℝ) : (∑ r, rowSurcharge α β δ r) = β + 90 * δ := by
  simp [rowSurcharge, Fintype.sum_sum_type, card_twoPaths]
  ring

lemma actualRowCost_nonneg {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7 * α ≤ β) (hd : 0 ≤ δ)
    (r : Row) : 0 ≤ actualRowCost α β δ r := by
  have hc : (0 : ℝ) ≤ rowCost r := by exact_mod_cast pattern.nonneg r
  exact add_nonneg hc (rowSurcharge_nonneg ha hb hd r)

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MetricProduct
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators ENNReal
namespace HyperbolicObstruction

namespace MetricProduct
universe u v
variable {ι : Type u} [Fintype ι] {X : ι → Type v} [∀ i, MetricSpace (X i)]

variable (h : ∀ i, CATZero (X i))

def segment (x y : PiLp 2 X) (t : ℝ) : PiLp 2 X :=
  WithLp.toLp 2 (fun i => CATZero.segment (h i) (x i) (y i) t)

omit [Fintype ι] in
lemma segment_apply (x y : PiLp 2 X) (t : ℝ) (i : ι) :
    segment h x y t i = CATZero.segment (h i) (x i) (y i) t := rfl

omit [Fintype ι] in
lemma segment_zero (x y : PiLp 2 X) : segment h x y 0 = x := by
  ext i
  exact (CATZero.segment_spec (h i) _ _).1

omit [Fintype ι] in
lemma segment_one (x y : PiLp 2 X) : segment h x y 1 = y := by
  ext i
  exact (CATZero.segment_spec (h i) _ _).2.1

lemma segment_dist (x y : PiLp 2 X) {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (segment h x y s) (segment h x y t) = |s - t| * dist x y := by
  have he : dist (segment h x y s) (segment h x y t) ^ 2 =
      (|s - t| * dist x y) ^ 2 := by
    rw [dist_sq, mul_pow, dist_sq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [segment_apply, segment_apply, CATZero.segment_dist (h i) _ _ hs ht, mul_pow]
  exact (sq_eq_sq₀ dist_nonneg (mul_nonneg (abs_nonneg _) dist_nonneg)).mp he

lemma segment_cn (x y z : PiLp 2 X) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist z (segment h x y t) ^ 2 ≤
      (1 - t) * dist z x ^ 2 + t * dist z y ^ 2 - t * (1 - t) * dist x y ^ 2 := by
  simp only [dist_sq, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i _ => CATZero.segment_cn (h i) _ _ _ ht

include h
/-- Finite L2 products preserve CAT(0), by summing the coordinate CN comparisons. -/
theorem catZero : CATZero (PiLp 2 X) := by
  intro x y
  exact ⟨segment h x y, ⟨segment_zero h x y, segment_one h x y,
    fun _ hs _ ht => segment_dist h x y hs ht⟩, fun z _ ht => segment_cn h x y z ht⟩

end MetricProduct
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
namespace MeanProduct
open scoped BigOperators
universe u v
variable (ι : Type u) [Fintype ι] [Nonempty ι]

variable (X : ι → Type v) [∀ i, MetricSpace (X i)]

variable {ι X}

variable (h : ∀ i, CATZero (X i))
include h

theorem catZero : CATZero (Space ι X) :=
  MetricScale.catZero (MetricProduct.catZero h)

end MeanProduct
end HyperbolicObstruction


noncomputable section
open Filter Topology
namespace HyperbolicObstruction
namespace MetricLimit
universe u
variable (U : Ultrafilter ℕ) (X : ℕ → Type u) [∀ n, MetricSpace (X n)] (o : ∀ n, X n)

variable {U X o}

variable (h : ∀ n, CATZero (X n))

/-- Coordinate segments are clamped outside the parameter interval, so the
boundedness obligation never relies on the arbitrary extension of a segment. -/
def segment (x y : Bounded U X o) (t : ℝ) : Bounded U X o :=
  if ht : t ∈ Set.Icc (0 : ℝ) 1 then
    ⟨fun n => CATZero.segment (h n) (x.val n) (y.val n) t, by
      obtain ⟨R, hR⟩ := x.bound
      obtain ⟨S, hS⟩ := y.bound
      refine ⟨2 * R + S, fun n => ?_⟩
      have hd : dist (x.val n) (y.val n) ≤ R + S :=
        (dist_triangle (x.val n) (o n) (y.val n)).trans (by
          rw [dist_comm (x.val n)]; exact add_le_add (hR n) (hS n))
      calc
        _ ≤ dist (o n) (x.val n) + dist (x.val n)
          (CATZero.segment (h n) (x.val n) (y.val n) t) := dist_triangle _ _ _
        _ = dist (o n) (x.val n) + t * dist (x.val n) (y.val n) := by
          rw [CATZero.segment_left (h n) _ _ ht]
        _ ≤ R + dist (x.val n) (y.val n) := add_le_add (hR n)
          (mul_le_of_le_one_left dist_nonneg ht.2)
        _ ≤ 2 * R + S := by linarith⟩
  else x

lemma segment_val (x y : Bounded U X o) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    (segment h x y t).val n = CATZero.segment (h n) (x.val n) (y.val n) t := by
  simp only [segment, dite_eq_left ht]

lemma segment_zero (x y : Bounded U X o) : segment h x y 0 = x := by
  apply Bounded.ext
  funext n
  rw [segment_val h x y (by norm_num)]
  exact (CATZero.segment_spec (h n) _ _).1

lemma segment_one (x y : Bounded U X o) : segment h x y 1 = y := by
  apply Bounded.ext
  funext n
  rw [segment_val h x y (by norm_num)]
  exact (CATZero.segment_spec (h n) _ _).2.1

lemma segment_dist (x y : Bounded U X o) {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (point (segment h x y s)) (point (segment h x y t)) =
      |s - t| * dist (point x) (point y) := by
  apply tendsto_nhds_unique (tendsto_point_dist _ _)
  convert (tendsto_point_dist x y).const_mul |s - t| using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [segment_val h x y hs, segment_val h x y ht, CATZero.segment_dist (h n) _ _ hs ht]

lemma segment_cn (x y z : Bounded U X o) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (point z) (point (segment h x y t)) ^ 2 ≤
      (1 - t) * dist (point z) (point x) ^ 2 + t * dist (point z) (point y) ^ 2 -
        t * (1 - t) * dist (point x) (point y) ^ 2 := by
  apply le_of_tendsto_of_tendsto ((tendsto_point_dist z (segment h x y t)).pow 2)
    ((((tendsto_point_dist z x).pow 2).const_mul (1 - t)).add
      (((tendsto_point_dist z y).pow 2).const_mul t) |>.sub
        (((tendsto_point_dist x y).pow 2).const_mul (t * (1 - t))))
  apply Filter.Eventually.of_forall
  intro n
  dsimp only
  rw [segment_val h x y ht]
  exact CATZero.segment_cn (h n) _ _ _ ht

include h

/-- CAT(0) comparison survives this metric ultralimit, proved directly from CN
and the convergence of every bounded pair of coordinate sections. -/
theorem catZero : CATZero (Space (U := U) (X := X) (o := o)) := by
  intro x y
  obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk x
  obtain ⟨y, rfl⟩ := SeparationQuotient.surjective_mk y
  refine ⟨fun t => point (segment h x y t), ⟨?_, ?_, ?_⟩, ?_⟩
  · dsimp only
    rw [segment_zero]
    rfl
  · dsimp only
    rw [segment_one]
    rfl
  · exact fun s hs t ht => segment_dist h x y hs ht
  · intro z t ht
    obtain ⟨z, rfl⟩ := SeparationQuotient.surjective_mk z
    exact segment_cn h x y z ht

end MetricLimit
end HyperbolicObstruction

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Graph
attribute [-instance] _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace MasterGraph
open IncidenceTemplate

namespace Step

def symm {a b : Vertex} (s : Step a b) : Step b a :=
  ⟨s.field, !s.forward, by
    have hs := s.endpoints
    cases h : s.forward <;> simp only [h, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte] at hs ⊢ <;> exact hs.symm⟩

end Step

/-- A fixed anchor and genuine paths in the finite literal core graph. -/
def root : Vertex := .inl (.inl 0)

end MasterGraph
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_GraphAction
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace MasterGraph
open IncidenceTemplate

namespace Path
variable {G L : Type*} [Group G] {a b c : Vertex}

def read (inv : L ≃ L) (σ : Field → Bool) (f : Field) : L ≃ L :=
  if σ f then Equiv.refl L else inv

end Path

/-- Actual consistency of the labelled graph in a group, not a metric
configuration or a conclusion of the sampling argument. -/
structure Potential {L G : Type*} [Group G] (label : Field → L) (letter : L → G) where
  val : Vertex → G
  root_one : val root = 1
  edge : ∀ f, val (target f) = val (source f) * letter (label f)

end MasterGraph
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Random
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
open scoped BigOperators

namespace TableModel
variable {F R A : Type*} [Fintype F] [Fintype R] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq A]

omit [Fintype F] [Fintype R] [Fintype A] [DecidableEq F] [DecidableEq R] [DecidableEq A] in
lemma row_injective (support : R → Finset F) (σ : F → A) :
    Function.Injective (row support σ) := by
  intro r s he
  exact congrArg Sigma.fst he

def law (support : R → Finset F) (p : R → ℝ)
    (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) :
    FiniteLaw (Entry (A := A) support → Bool) :=
  FiniteLaw.bernoulliProduct (fun e => p e.1) (fun e => hp e.1)

def IsMatch (support : R → Finset F) (w : Entry (A := A) support → Bool)
    (σ : F → A) : Prop := ∀ r, w (row support σ r) = true

instance instDecidableIsMatch (support : R → Finset F) (w : Entry (A := A) support → Bool) (σ : F → A) :
    Decidable (IsMatch support w σ) := inferInstanceAs (Decidable (∀ r, w (row support σ r) = true))

end TableModel
end HyperbolicObstruction

end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Moment
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction

namespace TableModel
variable {F R A : Type*} [Fintype F] [Fintype R] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq A]

lemma card_pinCandidates (P : Finset F) (ξ : F → A) :
    ((pinCandidates P ξ).card : ℝ) = (Fintype.card A : ℝ) ^ (Fintype.card F - P.card) := by
  rw [← sum_coincidence ξ P]
  simp [pinCandidates]

end TableModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SixCounts
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace SixTable
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

omit [Nonempty A] in
lemma card_pairTrials {r q : Fin 6} (h : r ≠ q) (u v : A) :
    ((pairTrials r q u v).card : ℝ) = (Fintype.card A : ℝ)^4 := by
  rw [pairTrials,TableModel.card_pinCandidates]
  simp [h,Finset.card_insert_of_notMem]

def law (δ : ℝ) (hδ : 0 ≤ δ) : FiniteLaw ((Fin 6 → A) → Bool) :=
  FiniteLaw.bernoulliProduct (fun _ => probability (A := A) δ) (fun _ => probability_mem hδ)

lemma pair_mean (δ : ℝ) {r q : Fin 6} (h : r ≠ q) (u v : A) :
    (∑ _ ∈ pairTrials r q u v, probability (A := A) δ) = (Fintype.card A : ℝ)^(1-δ) := by
  rw [Finset.sum_const,nsmul_eq_mul,card_pairTrials h]
  have hn : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos (α := A)
  rw [probability,← Real.rpow_natCast,← Real.rpow_add hn]
  congr 1
  ring

lemma centered_eq (δ : ℝ) {r q : Fin 6} (h : r ≠ q) (u v : A) (w : (Fin 6 → A) → Bool) :
    FiniteLaw.centeredCount (fun _ => probability (A := A) δ) (pairTrials r q u v) w =
      count r q u v w - (Fintype.card A : ℝ)^(1-δ) := by
  simp only [FiniteLaw.centeredCount,Finset.sum_sub_distrib,count,pair_mean δ h]

end SixTable
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StarModel
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R B A : Type*} [DecidableEq F]

def row [Nonempty B] (support : R → Finset F) (U : Finset F)
    (σ : Var (B := B) U → A) (s : Pos (B := B) support U) : TableModel.Entry (A := A) support :=
  ⟨array support U s, fun f => σ (coord U (branch support U s) f.val)⟩

lemma read_row [Nonempty B] [DecidableEq B] (support : R → Finset F) (U : Finset F)
    (σ τ : Var (B := B) U → A) (s : Pos (B := B) support U)
    (h : row support U σ s = row support U τ s) :
    ∀ v ∈ rowSupport support U s, σ v = τ v := by
  intro v hv
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hv
  have he : (fun f : support (array support U s) => σ (coord U (branch support U s) f.val)) =
      (fun f : support (array support U s) => τ (coord U (branch support U s) f.val)) := by
    exact eq_of_heq (Sigma.mk.inj h).2
  exact congrFun he ⟨f,hf⟩

lemma row_injective [Nonempty B] (support : R → Finset F) (U : Finset F)
    (σ : Var (B := B) U → A) (hσ : InjectiveFields U σ) :
    Function.Injective (row support U σ) := by
  intro s t he
  have ha : array support U s = array support U t := congrArg Sigma.fst he
  cases s with
  | inl r =>
    cases t with
    | inl q => exact congrArg Sum.inl (Subtype.ext ha)
    | inr jq => exact False.elim (jq.2.property ((show r.val = jq.2.val from ha) ▸ r.property))
  | inr jr =>
    cases t with
    | inl q => exact False.elim (jr.2.property ((show q.val = jr.2.val from ha.symm) ▸ q.property))
    | inr kq =>
      obtain ⟨j,r⟩ := jr
      obtain ⟨k,q⟩ := kq
      have hrq : r = q := Subtype.ext ha
      subst q
      have hf : ∃ f ∈ support r.val, f ∉ U := by simpa [Finset.subset_iff] using r.property
      obtain ⟨f,hf,hfu⟩ := hf
      have he' : (fun f : support r.val => σ (coord U j f.val)) =
          (fun f : support r.val => σ (coord U k f.val)) := eq_of_heq (Sigma.mk.inj he).2
      have hk := congrFun he' ⟨f,hf⟩
      have hjk : j = k := hσ ⟨f,hfu⟩ (by simpa [coord,hfu] using hk)
      subst k
      rfl

/-- Every actual branch is a master match exactly when every amalgamated row
trial is present. This identity permits the later coupling on actual matches. -/
lemma present_iff [Nonempty B] (support : R → Finset F) (U : Finset F)
    (σ : Var (B := B) U → A) (w : TableModel.Entry (A := A) support → Bool) :
    BernoulliCandidates.Present (row support U) w σ ↔
      ∀ j : B, TableModel.IsMatch support w (fun f => σ (coord U j f)) := by
  constructor
  · intro h j r
    by_cases hr : support r ⊆ U
    · have he : row support U σ (Sum.inl ⟨r,hr⟩) =
          TableModel.row support (fun f => σ (coord U j f)) r := by
        dsimp [row,TableModel.row,array,branch]
        congr 1
        funext f
        simp [coord,hr f.property]
      rw [← he]
      exact h _
    · exact h (Sum.inr (j,⟨r,hr⟩))
  · intro h s
    exact h (branch support U s) (array support U s)

end StarModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ExtensionMargin
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R B : Type*} [Fintype F] [Fintype R] [Fintype B]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [Nonempty B]

omit [DecidableEq R] in
lemma extension_selected_cost (P : SparsePattern.Pattern F R) (U : Finset F) (j₀ : B)
    (J : Finset (ExtPos P.support U j₀)) :
    let W := J.biUnion (fun s => rowSupport P.support U (extPos P.support U j₀ s))
    (∑ s ∈ J, P.cost s.2.val) ≤ ∑ j : {j : B // j ≠ j₀}, P.branchCost U U (wing U W j.val) := by
  dsimp only
  let W := J.biUnion (fun s => rowSupport P.support U (extPos P.support U j₀ s))
  have hh : ∀ s ∈ J, P.support s.2.val ⊆ U ∪ wing U W s.1.val := by
    intro s hs
    have he := (support_subset P.support U W (extPos P.support U j₀ s)).mp
      (show rowSupport P.support U (extPos P.support U j₀ s) ⊆ W from Finset.subset_biUnion_of_mem (fun t : ExtPos P.support U j₀ => rowSupport P.support U (extPos P.support U j₀ t)) hs)
    exact he.trans (Finset.union_subset_union_left (center_subset U W))
  calc
    _ = ∑ s ∈ J, if P.support s.2.val ⊆ U ∪ wing U W s.1.val then P.cost s.2.val else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [ite_eq_left (hh s hs)]
    _ ≤ ∑ s : ExtPos P.support U j₀, if P.support s.2.val ⊆ U ∪ wing U W s.1.val then P.cost s.2.val else 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intro s _ _; split_ifs; exact P.nonneg _; rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j _
      rw [sum_subtype_ite (fun r => ¬P.support r ⊆ U)
        (fun r => if P.support r ⊆ U ∪ wing U W j.val then P.cost r else 0)]
      change _ = P.branchCost U U (wing U W j.val)
      unfold SparsePattern.Pattern.branchCost
      apply Finset.sum_congr rfl
      intro r _
      by_cases h : P.support r ⊆ U <;> by_cases h' : P.support r ⊆ U ∪ wing U W j.val <;> simp [h,h']

omit [DecidableEq R] in
lemma extension_critical_gap (P : SparsePattern.Pattern F R) (U : Finset F) (j₀ : B)
    (gap : ∀ W, W.Nonempty → Disjoint U W → 1 ≤ P.exponent (U ∪ W) - P.exponent U)
    (J : Finset (ExtPos P.support U j₀)) (hJ : J.Nonempty) :
    1 ≤ (((J.biUnion (fun s => rowSupport P.support U (extPos P.support U j₀ s))) \ branchPins U j₀).card : ℤ) -
      ∑ s ∈ J, P.cost s.2.val := by
  let W := J.biUnion (fun s => rowSupport P.support U (extPos P.support U j₀ s))
  have hm := P.extension_margin (fun j : {j : B // j ≠ j₀} => wing_disjoint U W j.val)
    (extension_active P.support U j₀ J hJ) gap
  have hs := extension_selected_cost P U j₀ J
  rw [extension_free_card]
  push_cast
  simp only [Finset.sum_sub_distrib] at hm
  change 1 ≤ (∑ x : {j : B // j ≠ j₀}, ((wing U W x.val).card : ℤ)) - ∑ s ∈ J, P.cost s.2.val
  change (∑ s ∈ J, P.cost s.2.val) ≤ ∑ j : {j : B // j ≠ j₀}, P.branchCost U U (wing U W j.val) at hs
  omega

end StarModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Pinned
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace PinnedAssignments
variable {W F A : Type*} [Fintype W] [Fintype A]
  [DecidableEq W] [DecidableEq F] [DecidableEq A]

lemma candidates_lower (tag : W → F) (P : Finset W) (ξ : W → A)
    (hξ : PinFieldwise tag P ξ) (hN : 4 * Fintype.card W ≤ Fintype.card A) :
    ((Fintype.card A : ℝ) / 2) ^ Fintype.card (Free P) ≤ (candidates tag P ξ).card := by
  apply BernoulliCandidates.card_lower_half _ (P.image ξ) (embedding_mem tag P ξ hξ)
  have h₁ := Finset.card_image_le (s := P) (f := ξ)
  have h₂ := Finset.card_le_univ P
  have h₃ := Fintype.card_subtype_le (fun v : W => v ∉ P)
  change Fintype.card (Free P) ≤ Fintype.card W at h₃
  omega

end PinnedAssignments


end HyperbolicObstruction
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StarActual
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace IncidenceTemplate
variable {B : Type*} [Fintype B] [DecidableEq B] [Nonempty B]

omit [DecidableEq B] in
lemma star_surcharge {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7 * α ≤ β) (hd : 0 ≤ δ)
    (U : Finset Field) (J : Finset (StarModel.Pos (B := B) rowSupport U)) :
    (∑ s ∈ J, rowSurcharge α β δ (StarModel.array rowSupport U s)) ≤
      (Fintype.card B : ℝ) * (β + 90 * δ) := by
  rw [← rowSurcharge_sum]
  exact StarModel.sum_array_le rowSupport U _ (rowSurcharge_nonneg ha hb hd) J

end IncidenceTemplate

namespace PinnedAssignments
variable {W F A S I : Type*} [Fintype W] [Fintype F] [Fintype A] [Fintype S] [Fintype I]
  [DecidableEq W] [DecidableEq F] [DecidableEq A] [DecidableEq S] [DecidableEq I] [Nonempty A]

omit [Fintype F] in
/-- The generic variance estimate after pinning named coordinates, with the
cardinality bound produced from fieldwise injectivity. -/
theorem relative_variance (tag : W → F) (P : Finset W) (ξ : W → A)
    (hξ : PinFieldwise tag P ξ) (hN : 4 * Fintype.card W ≤ Fintype.card A)
    (row : (W → A) → S → I) (E : S → Finset W)
    (read : ∀ σ τ s, row σ s = row τ s → ∀ v ∈ E s, σ v = τ v)
    (inj : ∀ σ, Fieldwise tag σ → Function.Injective (row σ))
    (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (c : S → ℝ)
    (prob : ∀ σ s, p (row σ s) = (Fintype.card A : ℝ) ^ (-c s))
    {ε : ℝ} (gap : ∀ J : Finset S, J.Nonempty →
      ε ≤ (((J.biUnion E) \ P).card : ℝ) - ∑ s ∈ J, c s) :
    (FiniteLaw.bernoulliProduct p hp).variance
      (fun w => (BernoulliCandidates.count (fun σ => row (extend P ξ σ)) (candidates tag P ξ) w : ℝ)) ≤
    Fintype.card (BernoulliCandidates.OverlapType S) * 2 ^ Fintype.card (Free P) *
      (Fintype.card A : ℝ) ^ (-ε) *
      ((FiniteLaw.bernoulliProduct p hp).expect
        (fun w => (BernoulliCandidates.count (fun σ => row (extend P ξ σ)) (candidates tag P ξ) w : ℝ))) ^ 2 := by
  apply BernoulliCandidates.relative_variance_power
    (fun σ => row (extend P ξ σ)) (fun s => support P (E s))
    _ p hp (candidates tag P ξ) _ c _ (candidates_lower tag P ξ hξ hN)
  · intro J hJ
    rw [support_biUnion,card_support]
    exact gap J hJ
  · intro σ τ s he v hv
    have hh := read (extend P ξ σ) (extend P ξ τ) s he v.val ((mem_support _ _ _).mp hv)
    simpa only [extend_free] using hh
  · intro σ hσ
    exact inj _ (Finset.mem_filter.mp hσ).2
  · intro σ _ s
    exact prob _ s

end PinnedAssignments
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StarVariance
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R B A : Type*} [Fintype F] [Fintype R] [Fintype B] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [DecidableEq A] [Nonempty B]

abbrev leafCount (support : R → Finset F) (U : Finset F) (e : F) (ξ : Var (B := B) U → A) :=
  BernoulliCandidates.count
    (fun σ => row support U (PinnedAssignments.extend (leafPins U e) ξ σ))
    (PinnedAssignments.candidates (field U) (leafPins U e) ξ)

abbrev extensionCount (support : R → Finset F) (U : Finset F) (j₀ : B) (ξ : Var (B := B) U → A) :=
  BernoulliCandidates.count
    (fun σ s => row support U (PinnedAssignments.extend (branchPins U j₀) ξ σ) (extPos support U j₀ s))
    (PinnedAssignments.candidates (field U) (branchPins U j₀) ξ)

omit [Fintype F] [Fintype R] [Fintype B] [Fintype A]
    [DecidableEq R] [DecidableEq B] [DecidableEq A] in
lemma ext_injective (support : R → Finset F) (U : Finset F) (j₀ : B)
    (σ : Var (B := B) U → A) (hσ : PinnedAssignments.Fieldwise (field U) σ) :
    Function.Injective (fun s => row support U σ (extPos support U j₀ s)) :=
  (row_injective support U σ ((fieldwise_iff U σ).mp hσ)).comp (extPos_injective support U j₀)

end StarModel
namespace IncidenceTemplate

/-- Named finite instances avoid repeatedly synthesizing the literal nested subtype. -/
instance instRowFintype : Fintype Row := inferInstance
instance instFieldFintype : Fintype Field := inferInstance

variable {B A : Type*} [Fintype B] [Fintype A] [DecidableEq B] [DecidableEq A]
  [Nonempty B] [Nonempty A]

lemma star_extension_actual_gap {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7 * α ≤ β) (hd : 0 ≤ δ)
    (U : Finset Field) (j₀ : B)
    (gap : ∀ W, W.Nonempty → Disjoint U W → 1 ≤ pattern.exponent (U ∪ W) - pattern.exponent U)
    (J : Finset (StarModel.ExtPos rowSupport U j₀)) (hJ : J.Nonempty) :
    1 - (Fintype.card B : ℝ) * (β + 90 * δ) ≤
      (((J.biUnion (fun s => StarModel.rowSupport rowSupport U (StarModel.extPos rowSupport U j₀ s))) \ StarModel.branchPins U j₀).card : ℝ) -
        ∑ s ∈ J, actualRowCost α β δ s.2.val := by
  have hcrit := StarModel.extension_critical_gap pattern U j₀ gap J hJ
  have hc : (1 : ℝ) ≤
      (((J.biUnion (fun s => StarModel.rowSupport rowSupport U (StarModel.extPos rowSupport U j₀ s))) \ StarModel.branchPins U j₀).card : ℝ) -
        ∑ s ∈ J, (rowCost s.2.val : ℝ) := by exact_mod_cast hcrit
  have hs := StarModel.ext_surcharge_le rowSupport U j₀ (rowSurcharge α β δ) (rowSurcharge_nonneg ha hb hd) J
  rw [rowSurcharge_sum] at hs
  simp only [actualRowCost,Finset.sum_add_distrib]
  linarith

/-- Unconditioned variance for the residual trials of an extension. The next
conditioning identity identifies this with variance given the fixed match. -/
theorem extension_variance_bound {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7 * α ≤ β) (hd : 0 ≤ δ)
    (hsmall : (Fintype.card B : ℝ) * (β + 90 * δ) ≤ 1 / 2)
    (U : Finset Field) (j₀ : B)
    (gap : ∀ W, W.Nonempty → Disjoint U W → 1 ≤ pattern.exponent (U ∪ W) - pattern.exponent U)
    (ξ : StarModel.Var (B := B) U → A)
    (hN : 4 * Fintype.card (StarModel.Var (B := B) U) ≤ Fintype.card A) :
    let hp := fun r => TableModel.powerProbability_mem
      (show (1 : ℝ) ≤ Fintype.card A by exact_mod_cast Fintype.card_pos (α := A)) (actualRowCost_nonneg ha hb hd r)
    let μ := TableModel.law rowSupport (fun r => (Fintype.card A : ℝ) ^ (-actualRowCost α β δ r)) hp
    let X := fun w => (StarModel.extensionCount rowSupport U j₀ ξ w : ℝ)
    μ.variance X ≤ Fintype.card (BernoulliCandidates.OverlapType (StarModel.ExtPos rowSupport U j₀)) *
      2 ^ Fintype.card (PinnedAssignments.Free (StarModel.branchPins U j₀)) *
      (Fintype.card A : ℝ) ^ (-(1 / 2 : ℝ)) * μ.expect X ^ 2 := by
  apply PinnedAssignments.relative_variance (StarModel.field U) (StarModel.branchPins U j₀) ξ
    (StarModel.branch_pin_fieldwise U j₀ ξ) hN
    (fun σ s => StarModel.row rowSupport U σ (StarModel.extPos rowSupport U j₀ s))
    (fun s => StarModel.rowSupport rowSupport U (StarModel.extPos rowSupport U j₀ s))
    (fun σ τ s => StarModel.read_row rowSupport U σ τ (StarModel.extPos rowSupport U j₀ s))
    (StarModel.ext_injective rowSupport U j₀)
    _ _ (fun s => actualRowCost α β δ s.2.val) (fun _ _ => rfl)
  intro J hJ
  have hh := star_extension_actual_gap ha hb hd U j₀ gap J hJ
  linarith

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ExtensionConditioning
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R B A : Type*} [Fintype F] [Fintype R] [Fintype B] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [DecidableEq A] [Nonempty B]

omit [Fintype R] [DecidableEq R] in
lemma residual_ne_branch (support : R → Finset F) (U : Finset F) (j₀ : B)
    (ξ : Var (B := B) U → A) (σ : PinnedAssignments.Free (branchPins U j₀) → A)
    (hσ : σ ∈ PinnedAssignments.candidates (field U) (branchPins U j₀) ξ)
    (s : ExtPos support U j₀) (r : R) :
    row support U (PinnedAssignments.extend (branchPins U j₀) ξ σ) (extPos support U j₀ s) ≠
      TableModel.row support (fun f => ξ (coord U j₀ f)) r := by
  intro he
  have hr : s.2.val = r := congrArg Sigma.fst he
  subst r
  have hf : ∃ f ∈ support s.2.val, f ∉ U := by
    simpa [Finset.subset_iff] using s.2.property
  obtain ⟨f,hf,hfu⟩ := hf
  have hex : (fun f : support s.2.val =>
      PinnedAssignments.extend (branchPins U j₀) ξ σ (coord U s.1.val f.val)) =
      (fun f : support s.2.val => ξ (coord U j₀ f.val)) := eq_of_heq (Sigma.mk.inj he).2
  have hread := congrFun hex ⟨f,hf⟩
  have hpin : coord U j₀ f ∈ branchPins U j₀ := Finset.mem_image_of_mem _ (Finset.mem_univ f)
  have hp := PinnedAssignments.extend_pin (branchPins U j₀) ξ σ _ hpin
  have hi := (Finset.mem_filter.mp hσ).2
  have hcoord := hi (coord U s.1.val f) (coord U j₀ f) (by simp) (hread.trans hp.symm)
  have hj : s.1.val = j₀ := by simpa [coord,hfu] using hcoord
  exact s.1.property hj

lemma extension_depends (support : R → Finset F) (U : Finset F) (j₀ : B)
    (ξ : Var (B := B) U → A) (w z : TableModel.Entry (A := A) support → Bool)
    (hwz : ∀ i, i ∉ Finset.univ.image (TableModel.row support (fun f => ξ (coord U j₀ f))) → w i = z i) :
    extensionCount support U j₀ ξ w = extensionCount support U j₀ ξ z := by
  unfold extensionCount BernoulliCandidates.count
  congr 1
  apply Finset.filter_congr
  intro σ hσ
  have ht (s : ExtPos support U j₀) :
      w (row support U (PinnedAssignments.extend (branchPins U j₀) ξ σ) (extPos support U j₀ s)) =
      z (row support U (PinnedAssignments.extend (branchPins U j₀) ξ σ) (extPos support U j₀ s)) := by
    apply hwz
    rintro hm
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hm
    exact residual_ne_branch support U j₀ ξ σ hσ s r hr.symm
  simp only [BernoulliCandidates.Present,ht]

lemma leaf_expect (support : R → Finset F) (U : Finset F) (e : F)
    (ξ : Var (B := B) U → A) (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) :
    (TableModel.law support p hp).expect (fun w => (leafCount support U e ξ w : ℝ)) =
      (PinnedAssignments.candidates (field U) (leafPins U e) ξ).card *
        ∏ s : Pos (B := B) support U, p (array support U s) := by
  apply BernoulliCandidates.expect_count
  · intro σ hσ
    exact row_injective support U _ ((fieldwise_iff U _).mp (Finset.mem_filter.mp hσ).2)
  · intros; rfl

lemma extension_expect (support : R → Finset F) (U : Finset F) (j₀ : B)
    (ξ : Var (B := B) U → A) (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) :
    (TableModel.law support p hp).expect (fun w => (extensionCount support U j₀ ξ w : ℝ)) =
      (PinnedAssignments.candidates (field U) (branchPins U j₀) ξ).card *
        ∏ s : ExtPos support U j₀, p s.2.val := by
  apply BernoulliCandidates.expect_count
  · intro σ hσ
    exact ext_injective support U j₀ _ (Finset.mem_filter.mp hσ).2
  · intros; rfl

lemma leaf_expect_eq (support : R → Finset F) (U : Finset F) (e : F)
    (ξ ζ : Var (B := B) U → A) (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1)
    (hξ : PinnedAssignments.PinFieldwise (field U) (leafPins U e) ξ)
    (hζ : PinnedAssignments.PinFieldwise (field U) (leafPins U e) ζ) :
    (TableModel.law support p hp).expect (fun w => (leafCount support U e ξ w : ℝ)) =
      (TableModel.law support p hp).expect (fun w => (leafCount support U e ζ w : ℝ)) := by
  rw [leaf_expect,leaf_expect,PinnedAssignments.card_candidates_eq _ _ ξ ζ hξ hζ]

lemma extension_expect_eq (support : R → Finset F) (U : Finset F) (j₀ : B)
    (ξ ζ : Var (B := B) U → A) (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) :
    (TableModel.law support p hp).expect (fun w => (extensionCount support U j₀ ξ w : ℝ)) =
      (TableModel.law support p hp).expect (fun w => (extensionCount support U j₀ ζ w : ℝ)) := by
  rw [extension_expect,extension_expect,PinnedAssignments.card_candidates_eq _ _ ξ ζ
    (branch_pin_fieldwise U j₀ ξ) (branch_pin_fieldwise U j₀ ζ)]

end StarModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StarFiber
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R B A : Type*} [Fintype F] [Fintype R] [Fintype B] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [DecidableEq A] [Nonempty B]

omit [Fintype R] [Fintype B] [Fintype A] [DecidableEq R] [DecidableEq A] in
lemma fixed_branch_present (support : R → Finset F) (U : Finset F) (j₀ : B)
    (ξ : Var (B := B) U → A) (τ : PinnedAssignments.Free (branchPins U j₀) → A)
    (w : TableModel.Entry (A := A) support → Bool)
    (hm : TableModel.IsMatch support w (fun f => ξ (coord U j₀ f))) :
    BernoulliCandidates.Present (row support U) w (PinnedAssignments.extend (branchPins U j₀) ξ τ) ↔
      BernoulliCandidates.Present
        (fun τ s => row support U (PinnedAssignments.extend (branchPins U j₀) ξ τ) (extPos support U j₀ s)) w τ := by
  constructor
  · intro h s
    exact h _
  · intro h
    apply (present_iff support U _ w).mpr
    intro j r
    by_cases hr : support r ⊆ U
    · have he : TableModel.row support (fun f => PinnedAssignments.extend (branchPins U j₀) ξ τ (coord U j f)) r =
          TableModel.row support (fun f => ξ (coord U j₀ f)) r := by
        unfold TableModel.row
        congr 1
        funext f
        have hf := hr f.property
        have hc : coord U j f.val = coord U j₀ f.val := by simp [coord,hf]
        dsimp only
        rw [hc]
        exact PinnedAssignments.extend_pin _ _ _ _ (by
          exact Finset.mem_image_of_mem (coord U j₀) (Finset.mem_univ f.val))
      rw [he]
      exact hm r
    · by_cases hj : j = j₀
      · subst j
        have he : TableModel.row support (fun f => PinnedAssignments.extend (branchPins U j₀) ξ τ (coord U j₀ f)) r =
            TableModel.row support (fun f => ξ (coord U j₀ f)) r := by
          unfold TableModel.row
          congr 1
          funext f
          exact PinnedAssignments.extend_pin _ _ _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ f.val))
        rw [he]
        exact hm r
      · exact h (⟨j,hj⟩,⟨r,hr⟩)

abbrev Stars (support : R → Finset F) (U : Finset F)
    (w : TableModel.Entry (A := A) support → Bool) :=
  {σ : Var (B := B) U → A // PinnedAssignments.Fieldwise (field U) σ ∧ BernoulliCandidates.Present (row support U) w σ}

abbrev Matches (support : R → Finset F) (w : TableModel.Entry (A := A) support → Bool) :=
  {σ : F → A // TableModel.IsMatch support w σ}

instance instFintypeStars (support : R → Finset F) (U : Finset F) (w : TableModel.Entry (A := A) support → Bool) :
    Fintype (Stars (B := B) support U w) :=
  inferInstanceAs (Fintype {assignment : Var (B := B) U → A //
    PinnedAssignments.Fieldwise (field U) assignment ∧
      BernoulliCandidates.Present (row support U) w assignment})

instance instFintypeMatches (support : R → Finset F) (w : TableModel.Entry (A := A) support → Bool) :
    Fintype (Matches support w) :=
  inferInstanceAs (Fintype {assignment : F → A // TableModel.IsMatch support w assignment})

def starBranch (support : R → Finset F) (U : Finset F) (w : TableModel.Entry (A := A) support → Bool)
    (j : B) (σ : Stars (B := B) support U w) : Matches support w :=
  ⟨fun f => σ.val (coord U j f), (present_iff support U σ.val w).mp σ.property.2 j⟩

omit [DecidableEq R] in
/-- The fixed-match extension statistic is exactly the size of the branch fiber
of actual, present, fieldwise-injective stars. -/
theorem card_branch_fiber (support : R → Finset F) (U : Finset F)
    (w : TableModel.Entry (A := A) support → Bool) (j₀ : B) (σ : Matches support w) :
    Fintype.card {z : Stars (B := B) support U w // starBranch support U w j₀ z = σ} =
      extensionCount support U j₀ (branchValues U σ.val) w := by
  classical
  let ξ := branchValues (B := B) U σ.val
  let H : (Var (B := B) U → A) → Prop := BernoulliCandidates.Present (row support U) w
  let E := {z : Var (B := B) U → A // PinnedAssignments.Fieldwise (field U) z ∧
    (∀ v ∈ branchPins U j₀, z v = ξ v) ∧ H z}
  let e₁ : {z : Stars (B := B) support U w // starBranch support U w j₀ z = σ} ≃ E :=
    { toFun := fun z => ⟨z.val.val,z.val.property.1,
        (branch_eq_iff U j₀ ξ z.val.val).mp (fun f => by
          have hh := congrFun (congrArg Subtype.val z.property) f
          simpa [starBranch,ξ] using hh),z.val.property.2⟩
      invFun := fun z => ⟨⟨z.val,z.property.1,z.property.2.2⟩,by
        apply Subtype.ext
        funext f
        simpa [starBranch,ξ] using (branch_eq_iff U j₀ ξ z.val).mpr z.property.2.1 f⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hm : TableModel.IsMatch support w (fun f => ξ (coord U j₀ f)) := by
    simpa [ξ] using σ.property
  let e₂ := PinnedAssignments.fiberEquiv (field U) (branchPins U j₀) ξ H
  let C := PinnedAssignments.candidates (field U) (branchPins U j₀) ξ
  let row' := fun τ s => row support U (PinnedAssignments.extend (branchPins U j₀) ξ τ) (extPos support U j₀ s)
  let e₃ : {τ : PinnedAssignments.Free (branchPins U j₀) → A // τ ∈ C ∧ H (PinnedAssignments.extend (branchPins U j₀) ξ τ)} ≃
      ↥(C.filter (BernoulliCandidates.Present row' w)) :=
    { toFun := fun τ => ⟨τ.val,Finset.mem_filter.mpr ⟨τ.property.1,
        (fixed_branch_present support U j₀ ξ τ.val w hm).mp τ.property.2⟩⟩
      invFun := fun τ => ⟨τ.val,(Finset.mem_filter.mp τ.property).1,
        (fixed_branch_present support U j₀ ξ τ.val w hm).mpr (Finset.mem_filter.mp τ.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa only [Fintype.card_coe,extensionCount,BernoulliCandidates.count,C,row',ξ] using Fintype.card_congr ((e₁.trans e₂).trans e₃)

end StarModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LeafFiber
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R B A : Type*} [Fintype F] [Fintype R] [Fintype B] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [DecidableEq A] [Nonempty B]

def starLeaves (support : R → Finset F) (U : Finset F) (e : F) (he : e ∉ U)
    (w : TableModel.Entry (A := A) support → Bool) (z : Stars (B := B) support U w) : B ↪ A where
  toFun j := z.val (coord U j e)
  inj' := by
    intro j k h
    exact (fieldwise_iff U z.val).mp z.property.1 ⟨e,he⟩ (by simpa [coord,he] using h)

omit [DecidableEq R] in
/-- The leaf count is the exact fiber size of the uniform present-star law,
not the count of a surrogate independently resampled star. -/
theorem card_leaf_fiber (support : R → Finset F) (U : Finset F) (e : F) (he : e ∉ U)
    (w : TableModel.Entry (A := A) support → Bool) (b : B ↪ A) (a₀ : A) :
    Fintype.card {z : Stars (B := B) support U w // starLeaves support U e he w z = b} =
      leafCount support U e (leafValues U b a₀) w := by
  classical
  let ξ := leafValues U b a₀
  let H : (Var (B := B) U → A) → Prop := BernoulliCandidates.Present (row support U) w
  let E := {z : Var (B := B) U → A // PinnedAssignments.Fieldwise (field U) z ∧
    (∀ v ∈ leafPins U e, z v = ξ v) ∧ H z}
  let e₁ : {z : Stars (B := B) support U w // starLeaves support U e he w z = b} ≃ E :=
    { toFun := fun z => ⟨z.val.val,z.val.property.1,
        (leaves_eq_iff U e he b a₀ z.val.val).mp (fun j => by
          have hh := congrArg (fun f : B ↪ A => f j) z.property
          exact hh),z.val.property.2⟩
      invFun := fun z => ⟨⟨z.val,z.property.1,z.property.2.2⟩,by
        apply DFunLike.ext
        intro j
        exact (leaves_eq_iff U e he b a₀ z.val).mpr z.property.2.1 j⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e₂ := PinnedAssignments.fiberEquiv (field U) (leafPins U e) ξ H
  let C := PinnedAssignments.candidates (field U) (leafPins U e) ξ
  let row' := fun τ => row support U (PinnedAssignments.extend (leafPins U e) ξ τ)
  let e₃ : {τ : PinnedAssignments.Free (leafPins U e) → A // τ ∈ C ∧ H (PinnedAssignments.extend (leafPins U e) ξ τ)} ≃
      ↥(C.filter (BernoulliCandidates.Present row' w)) :=
    { toFun := fun τ => ⟨τ.val,Finset.mem_filter.mpr τ.property⟩
      invFun := fun τ => ⟨τ.val,Finset.mem_filter.mp τ.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa only [Fintype.card_coe,leafCount,BernoulliCandidates.count,C,row',ξ] using
    Fintype.card_congr ((e₁.trans e₂).trans e₃)

end StarModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Deviation
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R B A : Type*} [Fintype F] [Fintype R] [Fintype B] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [DecidableEq A] [Nonempty B]

def branchDeviation (support : R → Finset F) (U : Finset F) (j : B) (a : ℝ)
    (w : TableModel.Entry (A := A) support → Bool) : ℝ :=
  ∑ σ : F → A, if TableModel.IsMatch support w σ then
    |(extensionCount support U j (branchValues U σ) w : ℝ) - a| else 0

def leafDeviation (support : R → Finset F) (U : Finset F) (e : F) (a₀ : A) (b : ℝ)
    (w : TableModel.Entry (A := A) support → Bool) : ℝ :=
  ∑ a : B ↪ A, |(leafCount support U e (leafValues U a a₀) w : ℝ) - b|

omit [DecidableEq R] in
lemma branchDeviation_nonneg (support : R → Finset F) (U : Finset F) (j : B) (a : ℝ)
    (w : TableModel.Entry (A := A) support → Bool) : 0 ≤ branchDeviation support U j a w := by
  apply Finset.sum_nonneg
  intro σ _
  split_ifs <;> positivity

omit [DecidableEq R] in
lemma leafDeviation_nonneg (support : R → Finset F) (U : Finset F) (e : F) (a₀ : A) (b : ℝ)
    (w : TableModel.Entry (A := A) support → Bool) : 0 ≤ leafDeviation (B := B) support U e a₀ b w := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

end StarModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StarMean
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction

namespace StarModel
variable {F R B A : Type*} [Fintype F] [Fintype R] [Fintype B] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [DecidableEq A] [Nonempty B]

abbrev starCount (support : R → Finset F) (U : Finset F)
    (w : TableModel.Entry (A := A) support → Bool) := Fintype.card (Stars (B := B) support U w)

omit [DecidableEq R] in
lemma starCount_branch (support : R → Finset F) (U : Finset F) (j : B)
    (w : TableModel.Entry (A := A) support → Bool) :
    (starCount (B := B) support U w : ℝ) = ∑ σ : F → A, if TableModel.IsMatch support w σ then
      (extensionCount support U j (branchValues U σ) w : ℝ) else 0 := by
  classical
  calc
    _ = ∑ σ : Matches support w, (Fintype.card {z : Stars (B := B) support U w // starBranch support U w j z = σ} : ℝ) := by
      rw [← Nat.cast_sum,FiniteLaw.card_fibers]
    _ = ∑ σ : Matches support w, (extensionCount support U j (branchValues U σ.val) w : ℝ) := by
      simp only [card_branch_fiber]
    _ = _ := sum_subtype_eq_ite (TableModel.IsMatch support w)
      (fun σ : F → A => (extensionCount support U j (branchValues U σ) w : ℝ))

omit [DecidableEq R] in
lemma starCount_leaf (support : R → Finset F) (U : Finset F) (e : F) (he : e ∉ U)
    (w : TableModel.Entry (A := A) support → Bool) (a₀ : A) :
    (starCount (B := B) support U w : ℝ) = ∑ b : B ↪ A, (leafCount support U e (leafValues U b a₀) w : ℝ) := by
  classical
  calc
    _ = ∑ b : B ↪ A, (Fintype.card {z : Stars (B := B) support U w // starLeaves support U e he w z = b} : ℝ) := by
      rw [← Nat.cast_sum,FiniteLaw.card_fibers]
    _ = _ := by simp only [card_leaf_fiber (a₀ := a₀)]

omit [DecidableEq R] in
lemma branchDeviation_subtype (support : R → Finset F) (U : Finset F) (j : B) (a : ℝ)
    (w : TableModel.Entry (A := A) support → Bool) :
    branchDeviation support U j a w =
      ∑ σ : Matches support w, |(extensionCount support U j (branchValues U σ.val) w : ℝ) - a| :=
  (sum_subtype_eq_ite _ _).symm

lemma extensionMean_pos [Nonempty A] (support : R → Finset F) (U : Finset F) (j : B)
    (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (hpos : ∀ r, 0 < p r)
    (ξ : Var (B := B) U → A) (hN : 4 * Fintype.card (Var (B := B) U) ≤ Fintype.card A) :
    0 < (TableModel.law (A := A) support p hp).expect (fun w => (extensionCount support U j ξ w : ℝ)) := by
  rw [extension_expect]
  apply mul_pos
  · have hh := PinnedAssignments.candidates_lower (field U) (branchPins U j) ξ (branch_pin_fieldwise U j ξ) hN
    have hn : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos (α := A)
    exact lt_of_lt_of_le (pow_pos (half_pos hn) _) hh
  · exact Finset.prod_pos fun s _ => hpos s.2.val

end StarModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StarError
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction

namespace StarModel
variable {F R B A : Type*} [Fintype F] [Fintype R] [Fintype B] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [DecidableEq A] [Nonempty B]

/-- A single error statistic for the actual table, scaled by its nonrandom
expected star count. The leaf mean, not a fresh independent table, supplies the
normalizing-total estimate. -/
def normalizedError (support : R → Finset F) (U : Finset F) (e : F)
    (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (a₀ : A) (b₀ : B ↪ A)
    (w : TableModel.Entry (A := A) support → Bool) : ℝ :=
  let μ := TableModel.law (A := A) support p hp
  ((∑ j : B, branchDeviation support U j
    (μ.expect (fun w => (extensionCount support U j (fun _ => a₀) w : ℝ))) w) +
    leafDeviation (B := B) support U e a₀
      (μ.expect (fun w => (leafCount support U e (leafValues U b₀ a₀) w : ℝ))) w) /
    μ.expect (fun w => (starCount (B := B) support U w : ℝ))

lemma deviations_le_of_error (support : R → Finset F) (U : Finset F) (e : F)
    (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (a₀ : A) (b₀ : B ↪ A)
    (w : TableModel.Entry (A := A) support → Bool) {ε : ℝ}
    (hM : 0 < (TableModel.law (A := A) support p hp).expect (fun w => (starCount (B := B) support U w : ℝ)))
    (hε : normalizedError support U e p hp a₀ b₀ w ≤ ε) :
    (∀ j : B, branchDeviation support U j
      ((TableModel.law (A := A) support p hp).expect (fun w => (extensionCount support U j (fun _ => a₀) w : ℝ))) w ≤
      ε * (TableModel.law (A := A) support p hp).expect (fun w => (starCount (B := B) support U w : ℝ))) ∧
    leafDeviation (B := B) support U e a₀ ((TableModel.law (A := A) support p hp).expect
      (fun w => (leafCount support U e (leafValues U b₀ a₀) w : ℝ))) w ≤
      ε * (TableModel.law (A := A) support p hp).expect (fun w => (starCount (B := B) support U w : ℝ)) := by
  have hh := (div_le_iff₀ hM).mp hε
  constructor
  · intro j
    have hsum := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
      branchDeviation_nonneg support U j
        ((TableModel.law (A := A) support p hp).expect (fun w => (extensionCount support U j (fun _ => a₀) w : ℝ))) w)
      (Finset.mem_univ j)
    exact hsum.trans ((le_add_of_nonneg_right (leafDeviation_nonneg _ _ _ _ _ _)).trans hh)
  · exact (le_add_of_nonneg_left (Finset.sum_nonneg fun j _ => branchDeviation_nonneg _ _ _ _ _)).trans hh

end StarModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StarCoupling
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R A : Type*} [Fintype F] [Fintype R] [Fintype A]
  [DecidableEq F] [DecidableEq A] {k : ℕ}

/-- Forgetting the auxiliary injectivity retains an actual conditional star of
master matches. Its common tuple is named by I. -/
def toConditional (support : R → Finset F) (U I : Finset F) (hI : I ⊆ U)
    (w : TableModel.Entry (A := A) support → Bool) (z : Stars (B := Fin (k+1)) support U w) :
    ConditionalStar (fun a : Matches support w => a.val) I k :=
  ⟨fun j => starBranch support U w j z,by
    intro j f hf
    have hu := hI hf
    simp [starBranch,coord,hu]⟩

end StarModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StarRate
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate
variable {B A : Type*} [Fintype B] [Fintype A] [DecidableEq B] [DecidableEq A]
  [Nonempty B] [Nonempty A]

abbrev actualProbability (α β δ : ℝ) (A : Type*) [Fintype A] (r : Row) : ℝ :=
  (Fintype.card A : ℝ) ^ (-actualRowCost α β δ r)

omit [DecidableEq A] in
lemma actualProbability_mem {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ) (r : Row) :
    actualProbability α β δ A r ∈ Set.Icc (0:ℝ) 1 :=
  TableModel.powerProbability_mem
    (by exact_mod_cast Fintype.card_pos (α := A)) (actualRowCost_nonneg ha hb hd r)

omit [DecidableEq A] in
lemma actualProbability_pos (α β δ : ℝ) (r : Row) : 0 < actualProbability α β δ A r :=
  Real.rpow_pos_of_pos (by exact_mod_cast Fintype.card_pos (α := A)) _

def extensionRate (U : Finset Field) (j : B) (N : ℕ) : ℝ :=
  Fintype.card (BernoulliCandidates.OverlapType (StarModel.ExtPos rowSupport U j)) *
    2 ^ Fintype.card (PinnedAssignments.Free (StarModel.branchPins U j)) * (N : ℝ) ^ (-(1/2:ℝ))

def leafRate (U : Finset Field) (e : Field) (N : ℕ) : ℝ :=
  Fintype.card (BernoulliCandidates.OverlapType (StarModel.Pos (B := B) rowSupport U)) *
    2 ^ Fintype.card (PinnedAssignments.Free (StarModel.leafPins (B := B) U e)) * (N : ℝ) ^ (-(1/2:ℝ))

def errorRate (U : Finset Field) (e : Field) (N : ℕ) : ℝ :=
  (∑ j : B, Real.sqrt (extensionRate U j N)) + Real.sqrt (leafRate (B := B) U e N)

omit [Nonempty B] in
lemma errorRate_tendsto (U : Finset Field) (e : Field) :
    Tendsto (errorRate (B := B) U e) atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)^(-(1/2:ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/2)).comp tendsto_natCast_atTop_atTop
  have he (j : B) : Tendsto (fun N => Real.sqrt (extensionRate U j N)) atTop (𝓝 0) := by
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp (hn.const_mul
      ((Fintype.card (BernoulliCandidates.OverlapType (StarModel.ExtPos rowSupport U j)) : ℝ) *
        2 ^ Fintype.card (PinnedAssignments.Free (StarModel.branchPins U j))))
    simpa only [mul_zero,Real.sqrt_zero,Function.comp_def,extensionRate] using hh
  have hl : Tendsto (fun N => Real.sqrt (leafRate (B := B) U e N)) atTop (𝓝 0) := by
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp (hn.const_mul
      ((Fintype.card (BernoulliCandidates.OverlapType (StarModel.Pos (B := B) rowSupport U)) : ℝ) *
        2 ^ Fintype.card (PinnedAssignments.Free (StarModel.leafPins (B := B) U e))))
    simpa only [mul_zero,Real.sqrt_zero,Function.comp_def,leafRate] using hh
  unfold errorRate
  simpa only [Finset.sum_const_zero,zero_add] using
    (tendsto_finsetSum Finset.univ (fun j _ => he j)).add hl

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Test
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate

/-- A literal conditional test of Section 4, with k+1 branches. -/
structure ConditionalTest where
  fields : Finset Field
  leaf : Field
  newLeaf : leaf ∉ fields
  admissible : Admissible (insert leaf fields)
  k : ℕ

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TableSelection
attribute [-instance] _root_.OAI.HyperbolicObstruction.Coincidence.instDecidablePredForallBoolRankBad _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate
variable {J A : Type*} [Fintype J] [Fintype A] [DecidableEq A] [Nonempty A]

lemma alphabet_size_tendsto : Tendsto (fun n => Fintype.card (SymmetricAlphabet n)) atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ => n) _ tendsto_id
  intro n
  rw [card_symmetricAlphabet]
  omega

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkClasses
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]
namespace WalkPicture
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

noncomputable instance instFintypeVertex : Fintype P.Vertex := Fintype.ofFinite _

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FiniteSampling
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate

lemma admissible_singleton (e : Field) : Admissible {e} := by
  rcases e with e | ⟨τ,j⟩
  · left
    have hl : ({Sum.inl e} : Finset Field).toLeft = {e} := by ext; simp
    have hr : ({Sum.inl e} : Finset Field).toRight = ∅ := by ext; simp
    refine ⟨hr,?_,?_⟩
    · rw [hl]; simp
    · intro i
      rw [hl]
      have h := Finset.card_le_card (Finset.inter_subset_left : {e} ∩ fan i ⊆ {e})
      exact h.trans (by simp)
  · right
    refine ⟨τ,?_,by simp⟩
    rw [Finset.singleton_subset_iff]
    fin_cases j <;> simp [squareSupport]

/-- The finite named-field part of a conditional test. -/
abbrev ConditionalData := {p : Finset Field × Field // p.2 ∉ p.1 ∧ Admissible (insert p.2 p.1)}
instance instFintypeConditionalData : Fintype ConditionalData := Fintype.ofFinite _

abbrev ConditionalData.test (p : ConditionalData) (k : ℕ) : ConditionalTest :=
  ⟨p.val.1,p.val.2,p.property.1,p.property.2,k⟩

abbrev singletonData (e : Field) : ConditionalData :=
  ⟨(∅,e),by simp,by simpa using admissible_singleton e⟩

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Exceptional
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.IncidenceTemplate.instFieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open Filter Topology
namespace HyperbolicObstruction

namespace MasterGraph
open IncidenceTemplate OrbitLimit

def excC : Edge := ⟨(2,4), by decide⟩
def excY : Edge := ⟨(9,4), by decide⟩
def excD : Edge := ⟨(3,4), by decide⟩
def excI : Finset Field := { .inl excC, .inl excY }

universe u v w

end MasterGraph
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedWordPicture
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Persistent cell identities on word pictures. Unlike a bare relator witness,
this marking remembers which actual cell each interior face uses. -/
noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V : Type*}
  {R : Set (Word E)} {w : Word E}
  (B : PolygonTarget.Boundary C (E × Bool) V) (P : WordPicture R w)

structure Indexing where
  index : P.Dart → Option B.Side
  outside : ∀ x, index x = none ↔ x ∈ P.outside
  commute : ∀ x, index (P.pairing.face x) = (index x).map B.next
  injective : ∀ {x y : P.Dart}, P.pairing.face.SameCycle x y →
    ∀ s, index x = some s → index y = some s → x = y
  label : ∀ x s, index x = some s → P.label x = B.sideLabel s

namespace Indexing
variable {B P} (I : Indexing B P)

lemma commute_inv (x : P.Dart) :
    I.index (P.pairing.face⁻¹ x) = (I.index x).map B.next.symm := by
  have hh := I.commute (P.pairing.face⁻¹ x)
  simp only [Perm.inv_def,Equiv.apply_symm_apply] at hh
  rw [hh,Option.map_map]
  simp only [Function.comp_def,Perm.inv_def,Equiv.symm_apply_apply]
  cases I.index (P.pairing.face.symm x) <;> rfl

lemma reverse_prev (s : B.Side) : B.opposite (B.next⁻¹ s) = B.next (B.opposite s) := by
  have hh := congrArg B.next (B.reverse_next (B.next⁻¹ s))
  simpa only [Perm.inv_def,Equiv.apply_symm_apply] using hh.symm

variable {A : Type*} [AddCommGroup A]

/-- Count one marked corner of every interior face. Exterior corners contribute
zero. This uses independent cell coefficients, not the word image. -/
def cornerWeight (weight : C → A) (s : Option B.Side) : A :=
  match s with
  | none => 0
  | some s => if s.2.2.val = 0 then B.weight weight s else 0

def chain (weight : C → A) : A := ∑ x : P.Dart, cornerWeight weight (I.index x)

end Indexing
end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedPictureClosed
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V : Type*} {R : Set (Word E)}
  {B : PolygonTarget.Boundary C (E × Bool) V} {P : WordPicture R []}
namespace Indexing
variable (I : Indexing B P)

lemma closed_index_exists (x : P.Dart) : ∃ s, I.index x = some s := by
  have hout : P.outside = [] := List.map_eq_nil_iff.mp P.word
  cases hx : I.index x with
  | none => have hh := (I.outside x).mp hx; simp [hout] at hh
  | some s => exact ⟨s,rfl⟩

def closedIndex (x : P.Dart) : B.Side := (I.closed_index_exists x).choose
lemma closedIndex_spec (x : P.Dart) : I.index x = some (I.closedIndex x) :=
  (I.closed_index_exists x).choose_spec

lemma closed_mapped : IndexedFaceMap P.pairing.face B.next I.closedIndex := by
  constructor
  · intro x
    apply Option.some.inj
    rw [← I.closedIndex_spec, I.commute,I.closedIndex_spec]
    rfl
  · intro x y hxy he
    exact I.injective hxy (I.closedIndex x) (I.closedIndex_spec x)
      ((I.closedIndex_spec y).trans (congrArg some he.symm))

end Indexing
end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedPictureExistence
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal nullword disks with chosen persistent cell identities. -/
noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V : Type*} {R : Set (Word E)} {w : Word E}

abbrev InsideDart (P : WordPicture R w) := {x : P.Dart // x ∉ P.outside}

end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FinitePolygonModel
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite simplicial model of a literal finite polygon incidence system.
All edges are split three times, and every boundary occurrence has its own
collar vertex. Thus loops, repeated boundary vertices and parallel edges are
not silently identified. The carrier/homotopy comparison is a later theorem. -/
noncomputable section

namespace HyperbolicObstruction.FinitePolygonModel
open FinitePolyhedron

namespace Data
variable {V E C : Type*}
variable (P : Data V E C)

variable [DecidableEq V] [DecidableEq E] [DecidableEq C]

lemma simplex_card_le_three {s : Finset P.Vertex} (hs : s ∈ P.complex.faces) : s.card ≤ 3 := by
  have ht (a b c : P.Vertex) : ({a,b,c} : Finset P.Vertex).card ≤ 3 :=
    (Finset.card_insert_le a {b,c}).trans (Nat.add_le_add_right Finset.card_le_two 1)
  rcases hs.2 with h|⟨f,hf⟩
  · omega
  · apply (Finset.card_le_card hf).trans
    cases f with
    | inl e => dsimp [facet,graphFace]; split_ifs <;> exact Finset.card_le_two.trans (by decide)
    | inr q => dsimp [facet,collarFace]; split_ifs <;> exact ht _ _ _

end Data
end HyperbolicObstruction.FinitePolygonModel
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TriangleSquare
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! A literal closed triangle is the compact quotient of a square collapsing
only its upper edge. Continuous face homotopies therefore descend with their
three prescribed edge tracks. -/
noncomputable section
open scoped Topology unitInterval
open Topology
namespace HyperbolicObstruction.TriangleSquare

instance instCompactSpaceElemForallFinOfNatNatRealTriangle : CompactSpace Triangle := by
  refine isCompact_iff_compactSpace.mp
    (IsCompact.of_isClosed_subset
      (isCompact_Icc : IsCompact (Set.Icc (0 : Fin 3 → ℝ) 1)) ?_ ?_)
  · change IsClosed ({ coords : Fin 3 → ℝ | ∀ index, 0 ≤ coords index } ∩
      { coords | ∑ index, coords index = 1 })
    apply IsClosed.inter
    · rw [Set.ofPred_forall]
      exact isClosed_iInter (fun index => isClosed_le continuous_const (continuous_apply index))
    · exact isClosed_eq (by fun_prop) continuous_const
  · intro coords property
    exact ⟨property.1, fun index => coord_le_one ⟨coords, property⟩ index⟩

end HyperbolicObstruction.TriangleSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltageClosedCells
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed simplices in the actual voltage cover. The extended chart formula is
continuous even when its anchor coordinate is zero, by the triangle cocycle. -/
noncomputable section

open scoped Topology
open Set
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

instance totalSpace_t2 : T2Space v.TotalSpace := by
  apply t2Space_iff_disjoint_nhds.mpr
  intro e f hne
  by_cases hp : v.proj e = v.proj f
  · let j := v.core.indexAt e.proj
    let t := v.core.localTriv j
    have he : e ∈ t.source := t.mem_source.mpr (v.core.mem_baseSet_at e.proj)
    have hf : f ∈ t.source := t.mem_source.mpr (by
      change v.proj f ∈ openStar K j
      rw [←hp]
      exact v.core.mem_baseSet_at e.proj)
    have hn : t e ≠ t f := fun h => hne (t.injOn he hf h)
    exact (t.continuousAt he).disjoint (disjoint_nhds_nhds.mpr hn) (t.continuousAt hf)
  · exact v.core.continuous_proj.continuousAt.disjoint
      (disjoint_nhds_nhds.mpr hp) v.core.continuous_proj.continuousAt

lemma faceLift_injective {s : Finset V} (hs : s ∈ K.faces) {a : V}
    (ha : a ∈ s) (g : G) : Function.Injective (v.faceLift hs ha g) := by
  intro x y h
  exact Subtype.ext (congrArg v.proj h)

lemma faceLift_chart {s : Finset V} (hs : s ∈ K.faces) {a b : V}
    (ha : a ∈ s) (hb : b ∈ s) (g : G) (x : closedFace (K := K) s) :
    v.core.localTriv b (v.faceLift hs ha g x) = (x.val,g * v.value a b) := by
  apply Prod.ext
  · rfl
  change (g * v.value a (v.core.indexAt x.val)) * v.value (v.core.indexAt x.val) b = _
  rw [mul_assoc]
  congr 1
  apply v.triangle
  apply (K.isRelLowerSet_faces hs).2 _ (by simp)
  intro z hz
  simp only [Finset.mem_insert,Finset.mem_singleton] at hz
  rcases hz with rfl|rfl|rfl
  · exact ha
  · exact member_of_positive x (v.core.mem_baseSet_at x.val)
  · exact hb

def liftedClosedFace (q : FaceAnchor (K := K) × G) : Set v.TotalSpace :=
  Set.range (v.faceLift q.1.property.1 q.1.property.2 q.2)

lemma liftedClosedFace_cover : ⋃ q, v.liftedClosedFace q = Set.univ := by
  apply Set.eq_univ_of_forall
  intro e
  obtain ⟨s,hs,hx⟩ := e.proj.property.2.2
  have hxs : e.proj ∈ closedFace s := ⟨e.proj.property.1,e.proj.property.2.1,hx⟩
  let a := v.core.indexAt e.proj
  have ha : a ∈ s := member_of_positive ⟨e.proj,hxs⟩ (v.core.mem_baseSet_at e.proj)
  apply Set.mem_iUnion.mpr
  refine ⟨(⟨(s,a),hs,ha⟩,v.coordinate e),⟨e.proj,hxs⟩,?_⟩
  apply v.totalSpace_ext
  · rfl
  change v.coordinate e * v.value a a = v.coordinate e
  rw [v.self,mul_one]

/-- The original covering topology has a locally finite closed simplex cover.
There are only finitely many base faces/anchors and at most one deck label per
anchored face in a fixed small chart neighborhood. -/
lemma liftedClosedFace_locallyFinite : LocallyFinite v.liftedClosedFace := by
  intro e
  let j := v.core.indexAt e.proj
  let t := v.core.localTriv j
  have he : e ∈ t.source := t.mem_source.mpr (v.core.mem_baseSet_at e.proj)
  let U : Set v.TotalSpace := t.source ∩ (fun z => (t z).2) ⁻¹' {(t e).2}
  have hopen : IsOpen U := t.continuousOn.snd.isOpen_inter_preimage t.open_source (isOpen_discrete _)
  refine ⟨U,hopen.mem_nhds ⟨he,rfl⟩,?_⟩
  apply Set.Finite.of_injOn (f := Prod.fst) (t := Set.univ) (fun _ _ => Set.mem_univ _) ?_
    (Set.toFinite _)
  rintro ⟨q,g⟩ hq ⟨q',g'⟩ hq' hqq
  change q = q' at hqq
  subst q'
  obtain ⟨x,⟨z,rfl⟩,hx⟩ := hq
  obtain ⟨x',⟨z',rfl⟩,hx'⟩ := hq'
  have hj : j ∈ q.val.1 := member_of_positive z (t.mem_source.mp hx.1)
  have h1 := congrArg Prod.snd (v.faceLift_chart q.property.1 q.property.2 hj g z)
  have h2 := congrArg Prod.snd (v.faceLift_chart q.property.1 q.property.2 hj g' z')
  have hx0 : (t (v.faceLift q.property.1 q.property.2 g z)).2 = (t e).2 := hx.2
  have hx1 : (t (v.faceLift q.property.1 q.property.2 g' z')).2 = (t e).2 := hx'.2
  apply Prod.ext
  · rfl
  exact mul_right_cancel (h1.symm.trans (hx0.trans (hx1.symm.trans h2)))

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_EdgeCoordinates
attribute [-instance] _root_.OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.totalSpace_t2 _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal equality tests for barycentric edges. These prevent arbitrary
choices of edge homotopies from being silently identified at intersections. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [Fintype V] [DecidableEq V] (K : AbstractSimplicialComplex V)

lemma vertex_injective : Function.Injective (vertex K) := by
  intro a b hab
  by_contra hn
  have hh := congrArg (fun x : Carrier K => x.val a) hab
  simp [vertex,hn] at hh

lemma edgePath_coordinate {a b : V} (h : {a,b} ∈ K.faces) (s : I) (j : V) :
    (edgePath K h s).val j = (if j = a then 1-(s:ℝ) else 0) + (if j = b then (s:ℝ) else 0) := by
  change (AffineMap.lineMap (vertex K a).val (vertex K b).val (s:ℝ)) j = _
  simp [AffineMap.lineMap_apply_module,vertex,Pi.single_apply]

lemma edgePath_eq_vertex_cases {a b c : V} (h : {a,b} ∈ K.faces) (hab : a ≠ b)
    (s : I) (he : edgePath K h s = vertex K c) :
    (s = 0 ∧ a = c) ∨ (s = 1 ∧ b = c) := by
  have hc : c = a ∨ c = b := by
    by_contra hn
    push Not at hn
    have hh := congrArg (fun x : Carrier K => x.val c) he
    change (edgePath K h s).val c = (vertex K c).val c at hh
    rw [edgePath_coordinate] at hh
    simp [vertex,hn.1,hn.2] at hh
  rcases hc with hc|hc
  all_goals subst c
  · left
    refine ⟨Subtype.ext ?_,rfl⟩
    have hh := congrArg (fun x : Carrier K => x.val b) he
    change (edgePath K h s).val b = (vertex K _).val b at hh
    rw [edgePath_coordinate] at hh
    simpa [vertex,Pi.single_apply,hab,Ne.symm hab] using hh
  · right
    refine ⟨Subtype.ext ?_,rfl⟩
    have hh := congrArg (fun x : Carrier K => x.val b) he
    change (edgePath K h s).val b = (vertex K _).val b at hh
    rw [edgePath_coordinate] at hh
    simpa [vertex,Pi.single_apply,hab,Ne.symm hab] using hh

lemma edgePath_eq_edge_interior {a b c d : V} (h : {a,b} ∈ K.faces) (h' : {c,d} ∈ K.faces)
    (hab : a ≠ b) (hcd : c ≠ d) (s t : I) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (he : edgePath K h s = edgePath K h' t) :
    (a = c ∧ b = d ∧ s = t) ∨ (a = d ∧ b = c ∧ s = unitInterval.symm t) := by
  have hspos : 0 < (s:ℝ) := lt_of_le_of_ne s.property.1 (fun hz => hs0 (Subtype.ext hz.symm))
  have hslt : (s:ℝ) < 1 := lt_of_le_of_ne s.property.2 (fun hz => hs1 (Subtype.ext hz))
  have ha : a = c ∨ a = d := by
    by_contra hn
    push Not at hn
    have hh := congrArg (fun x : Carrier K => x.val a) he
    simp [edgePath_coordinate,hn.1,hn.2,hab] at hh
    linarith
  have hb : b = c ∨ b = d := by
    by_contra hn
    push Not at hn
    have hh := congrArg (fun x : Carrier K => x.val b) he
    simp [edgePath_coordinate,hn.1,hn.2,Ne.symm hab] at hh
    exact hs0 hh
  rcases ha with rfl|rfl <;> rcases hb with hb|hb
  · exact (hab hb.symm).elim
  · subst d
    left
    refine ⟨rfl,rfl,Subtype.ext ?_⟩
    have hh := congrArg (fun x : Carrier K => x.val b) he
    simpa [edgePath_coordinate,Ne.symm hab] using hh
  · subst c
    right
    refine ⟨rfl,rfl,Subtype.ext ?_⟩
    have hh := congrArg (fun x : Carrier K => x.val b) he
    simpa [edgePath_coordinate,Ne.symm hab] using hh
  · exact (hab hb.symm).elim

end HyperbolicObstruction.FinitePolyhedron
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SmallSimplexCoordinates
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Low-dimensional shared-face coordinates, in the actual barycentric carrier. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [Fintype V] [DecidableEq V] {K : AbstractSimplicialComplex V}

omit [DecidableEq V] in
lemma coordinate_le_one (x : Carrier K) (a : V) : x.val a ≤ 1 := by
  rw [←x.property.2.1]
  exact Finset.single_le_sum (fun i hi => x.property.1 i) (Finset.mem_univ a)

lemma simplex_sum_pair {a b : V} (hab : a ≠ b) (x : Voltage.closedFace (K := K) {a,b}) :
    x.val.val a + x.val.val b = 1 := by
  have hh := Finset.sum_subset (Finset.subset_univ ({a,b} : Finset V))
    (fun j hj hj' => x.property.2.2 j hj')
  simpa [Finset.sum_pair hab] using hh.trans x.property.2.1

namespace Voltage

def edgeParameter {a b : V} (x : closedFace (K := K) {a,b}) : I :=
  if a = b then 0 else ⟨x.val.val b,x.property.1 b,coordinate_le_one x.val b⟩

lemma edgeParameter_continuous (a b : V) :
    Continuous (edgeParameter (K := K) (a:=a) (b:=b)) := by
  unfold edgeParameter
  split_ifs
  · fun_prop
  · apply Continuous.subtype_mk
    exact (continuous_apply b).comp (continuous_subtype_val.comp continuous_subtype_val)

lemma edgePoint_parameter {a b : V} (h : {a,b} ∈ K.faces)
    (x : closedFace (K := K) {a,b}) : edgePoint h (edgeParameter x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  funext j
  change (edgePath K h (edgeParameter x)).val j = x.val.val j
  rw [edgePath_coordinate]
  by_cases hab : a = b
  · subst b
    have hh : x.val.val a = 1 := by
      have hh := Finset.sum_subset (Finset.subset_univ ({a} : Finset V))
        (fun j hj hj' => x.property.2.2 j (by simpa using hj'))
      simpa using hh.trans x.property.2.1
    by_cases hj : j = a
    · subst j; simp [edgeParameter,hh]
    · simp [hj,x.property.2.2 j (by simp [hj])]
  · have hsum := simplex_sum_pair hab x
    by_cases hj : j = a
    · subst j; simp [edgeParameter,hab]; linarith
    · by_cases hjb : j = b
      · subst j; simp [edgeParameter,hab,hj]
      · simp [hj,hjb,x.property.2.2 j (by simp [hj,hjb])]

lemma closedFace_inter {s t : Finset V} (x : Carrier K)
    (hs : x ∈ closedFace s) (ht : x ∈ closedFace t) : x ∈ closedFace (s ∩ t) := by
  refine ⟨hs.1,hs.2.1,?_⟩
  intro a ha
  by_cases hsa : a ∈ s
  · exact ht.2.2 a (fun hta => ha (Finset.mem_inter.mpr ⟨hsa,hta⟩))
  · exact hs.2.2 a hsa

omit [DecidableEq V] in
lemma closedFace_nonempty {s : Finset V} (x : closedFace (K := K) s) : s.Nonempty := by
  by_contra hn
  have hz : ∀ a, x.val.val a = 0 := fun a => x.property.2.2 a (fun ha => hn ⟨a,ha⟩)
  have hh := x.property.2.1
  simp [hz] at hh

end Voltage
end HyperbolicObstruction.FinitePolyhedron
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TriangleSquareFurther
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Topology unitInterval

namespace HyperbolicObstruction.TriangleSquare

lemma eq_bottom_of_zero (z : Triangle) (hz : z.val 2 = 0) :
    z = quotient (⟨z.val 1,z.property.1 1,coord_le_one z 1⟩,0) := by
  have hh := sum_coords z
  apply Subtype.ext
  rw [quotient_zero]
  apply funext; intro i; fin_cases i <;> dsimp
  all_goals first | exact hz | rfl | linarith
lemma eq_left_of_zero (z : Triangle) (hz : z.val 1 = 0) :
    z = quotient (0,⟨z.val 2,z.property.1 2,coord_le_one z 2⟩) := by
  have hh := sum_coords z
  apply Subtype.ext
  rw [quotient_left]
  apply funext; intro i; fin_cases i <;> dsimp
  all_goals first | exact hz | rfl | linarith
lemma eq_right_of_zero (z : Triangle) (hz : z.val 0 = 0) :
    z = quotient (1,⟨z.val 2,z.property.1 2,coord_le_one z 2⟩) := by
  have hh := sum_coords z
  apply Subtype.ext
  rw [quotient_right]
  apply funext; intro i; fin_cases i <;> dsimp
  all_goals first | exact hz | rfl | linarith

end HyperbolicObstruction.TriangleSquare
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltagePrismGluing
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine dimension-two contraction gluing theorem. Its local input is a
continuous prism for each face, compatible with the SAME edge prisms. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V] {K : AbstractSimplicialComplex V}
  {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  (v : Voltage K G)

lemma faceLift_sheet_injective {s : Finset V} (hs : s ∈ K.faces) {a : V} (ha : a ∈ s)
    (g k : G) (x y : closedFace (K := K) s)
    (he : v.faceLift hs ha g x = v.faceLift hs ha k y) : g = k ∧ x = y := by
  have hxy : x = y := Subtype.ext (congrArg v.proj he)
  subst y
  have h1 := congrArg Prod.snd (v.faceLift_chart hs ha ha g x)
  have h2 := congrArg Prod.snd (v.faceLift_chart hs ha ha k x)
  rw [he] at h1
  exact ⟨by simpa [v.self] using h1.symm.trans h2,rfl⟩

lemma edgeLift_exists {a b : V} (h : {a,b} ∈ K.faces) (e : v.TotalSpace)
    (he : v.proj e ∈ closedFace {a,b}) : ∃ g r, v.edgeLift h g r = e := by
  let x : closedFace (K := K) {a,b} := ⟨v.proj e,he⟩
  let g := v.coordinate e * (v.value a (v.core.indexAt (v.proj e)))⁻¹
  refine ⟨g,edgeParameter x,?_⟩
  have hp : edgePath K h (edgeParameter x) = v.proj e :=
    congrArg Subtype.val (edgePoint_parameter h x)
  rw [v.edgeLift_apply,hp]
  apply v.totalSpace_ext
  · rfl
  · simp [inChart_coordinate,g,mul_assoc]

lemma intersection_edge {s t : Finset V} (hs : s ∈ K.faces) (_ : t ∈ K.faces)
    (hsc : s.card ≤ 3) (htc : t.card ≤ 3) (hne : s ≠ t) (e : v.TotalSpace)
    (hx : v.proj e ∈ closedFace s) (hy : v.proj e ∈ closedFace t) :
    ∃ (a b : V) (h : {a,b} ∈ K.faces) (g : G) (r : I), v.edgeLift h g r = e := by
  have hxy := closedFace_inter (v.proj e) hx hy
  obtain ⟨a,b,hab⟩ := nonempty_pair_of_card_le_two
    (closedFace_nonempty (⟨v.proj e,hxy⟩ : closedFace (K := K) (s ∩ t)))
    (inter_card_le_two hsc htc hne)
  have he : {a,b} ∈ K.faces :=
    (K.isRelLowerSet_faces hs).2 (by rw [←hab]; exact Finset.inter_subset_left) (by simp)
  rw [hab] at hxy
  obtain ⟨g,r,hr⟩ := v.edgeLift_exists he e hxy
  exact ⟨a,b,he,g,r,hr⟩

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LoopSpaceReversal
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reversing the spatial coordinate of an actual two-loop negates its genuine
fundamental class in the compact-open loop space. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.LoopSpaceReversal
variable {X : Type*} [TopologicalSpace X] (b : X)
local notation "e" => (Path.refl b)

/-- The cancellation homotopy is continuous jointly in both parameters and
in the loop itself. -/
def cancel (u : Path e e) : (Path.refl e).Homotopy
    (HSpaceFundamental.combinePath u (reverse b u)) where
  toFun tx := (Path.Homotopy.reflTransSymm (u tx.2)).eval tx.1
  continuous_toFun := Path.continuous_uncurry_iff.mp (by
    change Continuous (fun z : (I × I) × I =>
      u z.1.2 ⟨Path.Homotopy.reflTransSymmAux (z.1.1,z.2),
        Path.Homotopy.reflTransSymmAux_mem_I (z.1.1,z.2)⟩)
    exact (Path.continuous_uncurry_iff.mpr u.continuous).comp
      ((continuous_snd.comp continuous_fst).prodMk
        ((Path.Homotopy.continuous_reflTransSymmAux.comp
          ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).subtype_mk _)))
  map_zero_left := by intro t; ext s; simp [Path.Homotopy.reflTransSymm]
  map_one_left := by
    intro t
    change (Path.Homotopy.reflTransSymm (u t)).eval 1 = _
    rw [Path.Homotopy.eval_one]
    rfl
  prop' := by
    intro t s hs
    rcases hs with hs|hs
    · subst s; ext r; simp [Path.Homotopy.reflTransSymm]; rfl
    · simp only [Set.mem_singleton_iff] at hs
      subst s; ext r; simp [Path.Homotopy.reflTransSymm]; rfl

lemma reverse_class (u : Path e e) :
    HSpacePathObstruction.loopClass (reverse b u) = (HSpacePathObstruction.loopClass u)⁻¹ := by
  have hh := Path.Homotopic.Quotient.eq.mpr (Nonempty.intro (cancel b u))
  have hz : HSpacePathObstruction.loopClass u * HSpacePathObstruction.loopClass (reverse b u) = 1 := by
    rw [←HSpacePathObstruction.loopClass_combine]
    exact hh.symm
  exact eq_inv_of_mul_eq_one_right hz

end HyperbolicObstruction.LoopSpaceReversal
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltageEdgeAgreement
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gluing of edge data is proved from the literal lifted coordinates. No
agreement of independent choices on intersecting edges is assumed. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

lemma vertexLift_eq_iff (a b : V) (g d : G) :
    v.vertexLift a g = v.vertexLift b d ↔ a = b ∧ g = d := by
  refine ⟨fun h => ⟨vertex_injective K (congrArg v.proj h),congrArg v.coordinate h⟩,?_⟩
  rintro ⟨rfl,rfl⟩; rfl
lemma edgeLift_sheet_injective {a b : V} (h : {a,b} ∈ K.faces) (s : I) :
    Function.Injective (fun g => v.edgeLift h g s) := by
  intro g d he
  have hh := congrArg v.coordinate he
  change g*v.value a (v.core.indexAt (edgePath K h s)) = d*v.value a (v.core.indexAt (edgePath K h s)) at hh
  exact mul_right_cancel hh

variable {X : Type*}
structure EdgeData where
  vertex : V → G → I → X
  edge : ∀ {a b : V}, {a,b} ∈ K.faces → G → I → I → X
  left : ∀ {a b : V} (h : {a,b} ∈ K.faces) g t, edge h g t 0 = vertex a g t
  right : ∀ {a b : V} (h : {a,b} ∈ K.faces) g t, edge h g t 1 = vertex b (g*v.value a b) t
  collapsed : ∀ a g t s, edge (edge_self K a) g t s = vertex a g t
  reversed : ∀ {a b : V} (h : {a,b} ∈ K.faces) g t s,
    edge (show {b,a} ∈ K.faces by simpa [Finset.pair_comm] using h) (g*v.value a b) t s =
      edge h g t (unitInterval.symm s)

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedFillingValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction

/-! The integral filling value of a literal nullword. This is a consequence
of constructed disks and sphere vanishing, not a replacement hypothesis. -/

/-! Literal walks in a signed incidence graph, with componentwise root paths.
No connectedness or universal-cover assertion is assumed. -/

namespace SignedWalks

section
open HyperbolicObstruction.WordPictures
variable {E V : Type*} (start : E × Bool → V)

inductive Walk : V → V → Word E → Prop
  | nil (x) : Walk x x []
  | cons (e : E × Bool) {y : V} {w : Word E} :
      Walk (start (invLetter e)) y w → Walk (start e) y (e::w)

namespace Walk
variable {start} {x y z : V} {u v : Word E}

lemma single (e : E × Bool) : Walk start (start e) (start (invLetter e)) [e] :=
  .cons e (.nil _)

lemma append (hu : Walk start x y u) (hv : Walk start y z v) : Walk start x z (u++v) := by
  induction hu with
  | nil => exact hv
  | cons e h ih => exact .cons e (ih hv)

lemma reverse (h : Walk start x y u) : Walk start y x (FreeGroup.invRev u) := by
  induction h with
  | nil x => exact .nil x
  | cons e h ih =>
    rw [FreeGroup.invRev_cons]
    have hs := single (start := start) (invLetter e)
    rw [invLetter_invLetter] at hs
    exact ih.append hs

end Walk

/-- Reachability in the actual signed graph, not equality of word images. -/
def reach : Setoid V where
  r x y := ∃ w, Walk start x y w
  iseqv := ⟨fun x => ⟨[],.nil x⟩,
    fun ⟨w,h⟩ => ⟨FreeGroup.invRev w,h.reverse⟩,
    fun ⟨u,hu⟩ ⟨v,hv⟩ => ⟨u++v,hu.append hv⟩⟩

def root (x : V) : V := Quotient.out (Quotient.mk (reach start) x)
lemma root_reach (x : V) : (reach start).r (root start x) x :=
  Quotient.exact (Quotient.out_eq _)

def rootWord (x : V) : Word E := (root_reach start x).choose

def correction (e : E × Bool) : Word E :=
  rootWord start (start e) ++ [e] ++ FreeGroup.invRev (rootWord start (start (invLetter e)))

end

open HyperbolicObstruction.WordPictures

end SignedWalks

/-! A literal disk-chain left inverse for the integral cell boundary. The
rooted-edge construction avoids assuming an arbitrary-cycle sphere producer. -/

namespace IndexedFilling
open HyperbolicObstruction.WordPictures HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch SignedWalks
attribute [local instance] Classical.propDecidable
variable {C E V A : Type*} [AddCommGroup A]
  (B : PolygonTarget.Boundary C (E × Bool) V) (weight : C → A)

def cellBoundary (c : C) : E →₀ ℤ := ∑ i, letterChain (B.label c i)
def boundary : (C →₀ ℤ) →ₗ[ℤ] (E →₀ ℤ) := Finsupp.linearCombination ℤ (cellBoundary B)

end IndexedFilling

/-! Subdivision of permutation cycles, with exact orbit-count preservation. -/

/-! Local elementary triangle incidence induces the exact radial contraction. -/

/-! Lifting actual word homotopies to the voltage cover, with the negative
orientation based at the positive lift's initial endpoint. -/
namespace VoltageWords

section
open HyperbolicObstruction.WordPictures
variable {A G : Type*} [Group G]

/-- Relators of the actual voltage-cover edge presentation, not a quotient of
base-cell coefficients. Every deck coordinate remains an independent index. -/
def Relators (v : A → G) (R : Set (Word A)) : Set (Word (G × A)) :=
  {z | ∃ g w, w ∈ R ∧ z = liftWord v g w}

end

open HyperbolicObstruction.WordPictures HyperbolicObstruction.PictureSwitch

end VoltageWords

/-!
The actual elementary triangles imply the compressed cone polygon equations.
Unlike the redundant polygon bouquet, this presentation retains exactly the
elementary indexed top triangles.
-/

/-! Actual genus-zero disks for every closed elementary loop in the original
letter voltage cover. No cycle-representation or asphericity hypothesis. -/

/-! No reselection: the same final arrays already have the precise uniform
lifted-picture estimate. Apply the new disk-chain left inverse to those arrays. -/

/-! The actual elementary incidence data now defines an actual finite
barycentric polyhedron. This file proves compactness and connectivity only;
no CW-universal-cover comparison is smuggled in as a structure field. -/

/-! Restricting any flat voltage on the actual triangulation to the original
indexed graph. Literal cap triangles prove every original boundary relation. -/

/-! Genuine continuous fundamental groups are generated by the finite edges. -/

/-! New subdivision, collar and cone edges do not create fundamental-group
generators. This concerns the actual barycentric realization. -/

/-! The literal polygon presentation maps to the actual pi1, and its tree
normalization has no hidden van Kampen hypothesis. -/

/-! Identification of the actual finite elementary polyhedron's pi1 with the
original letter presentation, using actual path classes and voltage covers. -/

/-! The actual voltage cover is universal whenever its proved monodromy
comparison is bijective. No simple-connectivity premise on the total space
is substituted for the producer. -/

/-! The literal voltage bundle is an actual simply connected covering
of the actual finite polygon realization. We construct its connectivity from
monodromy, rather than naming an abstract universal cover as a hypothesis. -/

/-! Exact higher homotopy identification for the constructed simply connected
voltage covering of the actual frozen finite polyhedron. -/

section

/-! Literal area-counted edge-disk calculus on the frozen finite-complex
model. All path algebra below uses only the challenge's stutters and spurs. -/
namespace FinitePolyhedron.EdgeChain
open HyperbolicObstruction.FiniteComplex
variable {K : FiniteComplex}

def steps {a b : K.Vertex} : K.Chain a b → List K.Vertex
  | .nil _ => []
  | .cons (b := b) _ p => b :: p.steps

end FinitePolyhedron.EdgeChain
end

/-! Rooted path algebra with exact zero-cost spur cancellations. This is a
literal triangular disk calculus, not an appeal to topological equivalence. -/

/-! Quantitative finite-presentation change, with all word substitutions and
comparison disks constructed. Relator disks are used only after establishing
that the corresponding literal words are null. -/
namespace WordPictures
variable {A B G : Type*} [Group G]

def signedWords (f : A → Word B) (a : A × Bool) : Word B :=
  if a.2 then f a.1 else FreeGroup.invRev (f a.1)

/-! Finite change of presentation preserves the literal linear disk bound.
All finite comparison disks are produced by ordinary algebraic van Kampen
existence; they are not introduced as extra geometric hypotheses. -/

end WordPictures

/-! Literal finite relator words for the proved actual fundamental-group
presentation, including exact rooted route words. -/

/-! Realization of ordinary word disks as literal triangular edge disks over
the frozen finite polyhedron. Free-group folds become actual zero-cost spurs. -/

/-! Group-isomorphism transport for geometric actions. -/
section
universe u v w
namespace GeometricAction
variable {G : Type v} {H : Type w} [Group G] [Group H]
  {X : Type u} [MetricSpace X]

def pullback (e : G ≃* H) (A : GeometricAction H X) : GeometricAction G X where
  act := A.act.comp e.toMonoidHom
  proper C hC := by
    have hfin := A.proper C hC
    change (e ⁻¹' {g : H | ∃ x ∈ C, A.act g x ∈ C}).Finite
    exact Set.Finite.preimage e.injective.injOn hfin
  cocompact := by
    obtain ⟨C,hC,hcov⟩ := A.cocompact
    refine ⟨C,hC,fun x => ?_⟩
    obtain ⟨g,y,hy,he⟩ := hcov x
    exact ⟨e.symm g,y,hy,by simpa using he⟩
end GeometricAction

end

/-! Actual homotopy-equivalence invariance of the fundamental group. -/

/-! The literal finite barycentric complex has exactly the original letter group,
not a conditional presentation of it. -/

/-! The same supplied final arrays yield infinite groups unconditionally.
This discharges the last group-action-side hypothesis; the finite-polyhedron
realization and group-to-topology consequences are still separate obligations. -/

/-! Elementary facts about WordLength and WordDistance for the four-point
characterization of hyperbolicity. -/

/-! Cochains are evaluated on the actual area-counted word homotopies.
Free folds contribute exactly zero; each literal relator contributes its
own cochain integral. No planar realization hypothesis is needed. -/

/-! Finite unit-speed vertex paths; all indices are bounded explicitly. -/
section
open Finset
namespace VertexPath
variable {X : Type*}

variable [MetricSpace X]
def Quasi (p : VertexPath X) (c : ℝ) : Prop :=
  ∀ i ≤ p.length, ∀ j ≤ p.length, |(i:ℝ)-j|  ≤  c*dist (p.point i) (p.point j)
def Geodesic (p : VertexPath X) : Prop :=
  ∀ i ≤ p.length, ∀ j ≤ p.length, dist (p.point i) (p.point j)=|(i:ℝ)-j|

end VertexPath
end

namespace VertexPath

section
variable {X : Type*} [MetricSpace X]
def between (p : VertexPath X) (i j : ℕ) : VertexPath X :=
  if i ≤ j then p.sub i j else (p.sub j i).reverse

end

variable {X : Type*} [MetricSpace X]

/-- Literal vertex thin triangles. -/
def ThinTriangles (X : Type*) [MetricSpace X] (D : ℝ) : Prop :=
  ∀ p q r : VertexPath X, p.Geodesic → q.Geodesic → r.Geodesic →
    p.start=q.start → p.finish=r.start → q.finish=r.finish →
    ∀ i ≤ p.length, (∃ j ≤ q.length, dist (p.point i) (q.point j) ≤ D) ∨
      (∃ j ≤ r.length, dist (p.point i) (r.point j) ≤ D)

end VertexPath

/-! A quantitative proof that linear word-homotopy filling bounds imply
four-point hyperbolicity. -/

/-! All clauses of the exact main except exclusion of compatible locally
CAT(-1) finite homotopy models. The complete literal hyperbolicity consequence
is now unconditional, on the SAME finite aspherical complex. -/

/-! The real comparison inequality needed to pass the manuscript's exact
cosh-midpoint CAT(-1) definition to the Euclidean CN midpoint inequality. -/

/-! The global cosh-midpoint comparison implies whole-segment CAT(0)
comparison. No completeness or globalization
hypothesis is hidden in this elementary curvature-monotonicity step. -/

section

/-! Uniform local comparison, extracted from compactness and the precise
hypothetical metric in the main. The midpoint is an actual ambient midpoint;
its local uniqueness and estimates are proved, not postulated. -/
open Set Metric
variable {X : Type*} [MetricSpace X]

/-- A uniform ambient neighborhood lies in a CAT(0) subspace. -/
def UniformLocalCATZero (r : ℝ) : Prop :=
  ∀ x : X, ∃ U : Set X, ball x r ⊆ U ∧ CATZero U

lemma midpoint_eq_subtype {U : Set X} (hU : CATZero U) (g : IsGeodesic X)
    {a b : X} (ha : a ∈ U) (hb : b ∈ U) (hm : g.midpoint a b ∈ U) :
    (⟨g.midpoint a b,hm⟩ : U) = CATZero.mid hU ⟨a,ha⟩ ⟨b,hb⟩ := by
  apply CATZero.eq_segment_of_dist hU (by norm_num : (1/2:ℝ) ∈ Icc 0 1)
  · change dist a (g.midpoint a b) = (1/2)*dist a b
    rw [g.dist_left_midpoint]
    simp [div_eq_mul_inv,mul_comm]
  · change dist (g.midpoint a b) b = (1-1/2)*dist a b
    rw [g.dist_midpoint_right]
    norm_num
    ring

lemma UniformLocalCATZero.midpoint_lipschitz {r : ℝ} (h : UniformLocalCATZero (X:=X) r)
    (g : IsGeodesic X) {o a b c d : X}
    (ha : a ∈ ball o (r/3)) (hb : b ∈ ball o (r/3))
    (hc : c ∈ ball o (r/3)) (hd : d ∈ ball o (r/3)) :
    dist (g.midpoint a b) (g.midpoint c d) ≤ (dist a c+dist b d)/2 := by
  have hr : 0 < r := by have hh := dist_nonneg (x:=a) (y:=o); rw [mem_ball] at ha; linarith
  obtain ⟨U,hU,hcat⟩ := h o
  have sub : ball o (r/3) ⊆ U := (ball_subset_ball (by linarith)).trans hU
  have hm₁ := midpoint_eq_subtype hcat g (sub ha) (sub hb) (hU (g.midpoint_mem_ball ha hb))
  have hm₂ := midpoint_eq_subtype hcat g (sub hc) (sub hd) (hU (g.midpoint_mem_ball hc hd))
  have hh := CATZero.dist_mid_mid_le hcat (⟨a,sub ha⟩ : U) ⟨b,sub hb⟩ ⟨c,sub hc⟩ ⟨d,sub hd⟩
  rw [←hm₁,←hm₂] at hh
  exact hh

end

/-! The finite difference maximum principle required for local geodesic
continuation. Endpoint estimates are literal, with no convergence assumption. -/

section

/-! Actual finite local-geodesic continuation. Uniform local comparison and
compactness produce, rather than assume, stationary polygons with perturbed
endpoints, and the finite maximum principle produces their uniqueness. -/
open Metric
namespace LocalPolygonContinuation
open FiniteMidpointFixedPoint
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  {r : ℝ} (hr : 0 < r) (hcat : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
  {n : ℕ} (q : Fin (n+2) → X)
  (hnear : ∀ i : Fin n, dist (q (left i)) (q (center i)) < r/10 ∧
    dist (q (right i)) (q (center i)) < r/10)
  (hmid : ∀ i : Fin n, q (center i)=g.midpoint (q (left i)) (q (right i)))

include hr in
omit [CompactSpace X] in
lemma box_nonempty {a b : X} (ha : dist a (q 0) ≤ r/20)
    (hb : dist b (q (Fin.last (n+1))) ≤ r/20) : (Box (r:=r) q a b).Nonempty := by
  classical
  let p : Fin (n+2) → X := fun i => if i=0 then a else if i=Fin.last (n+1) then b else q i
  have hn : (Fin.last (n+1) : Fin (n+2))≠0 := by intro he; have := congrArg Fin.val he; simp at this
  refine ⟨p,by simp [p],by simp [p,hn],?_⟩
  intro i
  by_cases h0 : i=0
  · subst i; simpa [p] using ha
  by_cases hl : i=Fin.last (n+1)
  · subst i; simpa [p,hn] using hb
  simp only [p,ite_eq_right h0,ite_eq_right hl,dist_self]
  linarith

omit [CompactSpace X] in
lemma node_center {a b : X} (p : Box (r:=r) q a b) (i : Fin n) :
    node g q p (center i)=g.midpoint (p.val (left i)) (p.val (right i)) := by
  have h0 : center i≠0 := by intro he; have := congrArg Fin.val he; simp [center] at this
  have hl : center i≠Fin.last (n+1) := by
    intro he; have hh := congrArg Fin.val he; dsimp [center] at hh; omega
  simp only [node,dite_eq_right h0,dite_eq_right hl]
  congr 2

include hr hcat hnear hmid in
omit [CompactSpace X] in
lemma node_mem {a b : X} (ha : dist a (q 0) ≤ r/20)
    (hb : dist b (q (Fin.last (n+1))) ≤ r/20) (p : Box (r:=r) q a b) :
    node g q p ∈ Box (r:=r) q a b := by
  refine ⟨node_zero g q p,node_last g q p,fun i => ?_⟩
  by_cases h0 : i=0
  · subst i; simpa only [node_zero] using ha
  by_cases hl : i=Fin.last (n+1)
  · subst i; simpa only [node_last] using hb
  have hi0 : 0 < i.val := by by_contra hh; apply h0; apply Fin.ext; simp only [Fin.val_zero]; omega
  have hin : i.val < n+1 := by by_contra hh; apply hl; apply Fin.ext; simp; omega
  let j : Fin n := ⟨i.val-1,by omega⟩
  have he : center j=i := by apply Fin.ext; dsimp [center,j]; omega
  rw [←he,node_center,hmid j]
  have hp := neighbors_in_ball hr q hnear p j
  have hq₁ : q (left j) ∈ ball (q (center j)) (r/3) := by rw [mem_ball]; linarith [(hnear j).1]
  have hq₂ : q (right j) ∈ ball (q (center j)) (r/3) := by rw [mem_ball]; linarith [(hnear j).2]
  have hh := hcat.midpoint_lipschitz g hp.1 hp.2 hq₁ hq₂
  linarith [p.property.2.2 (left j),p.property.2.2 (right j)]

include hr hcat hnear hmid in
/-- Small endpoint perturbations have an actual midpoint-stationary polygon
in the prescribed box. Compactness is used only for a genuine finite minimum. -/
theorem exists_stationary {a b : X} (ha : dist a (q 0) ≤ r/20)
    (hb : dist b (q (Fin.last (n+1))) ≤ r/20) :
    ∃ p : Fin (n+2) → X, p ∈ Box (r:=r) q a b ∧
      ∀ i : Fin n, p (center i)=g.midpoint (p (left i)) (p (right i)) := by
  let B := Box (r:=r) q a b
  have : CompactSpace B := isCompact_iff_compactSpace.mp (box_closed q a b).isCompact
  have : Nonempty B := Set.nonempty_coe_sort.mpr (box_nonempty hr q ha hb)
  let T : B → B := fun p => ⟨node g q p,node_mem hr hcat g q hnear hmid ha hb p⟩
  have hT (i : Fin (n+2)) : Continuous (fun p : B => (T p).val i) := by
    by_cases h0 : i=0
    · subst i; simpa [T,node_zero] using (continuous_const : Continuous (fun _ : B => a))
    by_cases hn : i=Fin.last (n+1)
    · subst i; simpa [T,node_last] using (continuous_const : Continuous (fun _ : B => b))
    have hil : 0 < i.val := by by_contra hh; apply h0; apply Fin.ext; simp only [Fin.val_zero]; omega
    have hin : i.val < n+1 := by by_contra hh; apply hn; apply Fin.ext; simp; omega
    let j : Fin n := ⟨i.val-1,by omega⟩
    have he : center j=i := by apply Fin.ext; dsimp [center,j]; omega
    have hLip : LipschitzWith 1 (fun p : B => (T p).val i) := by
      apply LipschitzWith.of_dist_le_mul
      intro p s
      change dist (node g q p i) (node g q s i) ≤ _
      rw [←he,node_center,node_center]
      have hp := neighbors_in_ball hr q hnear p j
      have hs := neighbors_in_ball hr q hnear s j
      have hh := hcat.midpoint_lipschitz g hp.1 hp.2 hs.1 hs.2
      have h1 : dist (p.val (left j)) (s.val (left j))≤dist p s := dist_le_pi_dist p.val s.val _
      have h2 : dist (p.val (right j)) (s.val (right j))≤dist p s := dist_le_pi_dist p.val s.val _
      norm_num
      linarith
    exact hLip.continuous
  obtain ⟨p,hp⟩ := FiniteMidpointFixedPoint.exists_fixed n (fun p : B => p.val)
    (fun i => (continuous_apply i).comp continuous_subtype_val) Subtype.val_injective T hT
    (fun p s => by simp [T,node_zero]) (fun p s => by simp [T,node_last])
    (fun p s i => by
      change dist (node g q p (center i)) (node g q s (center i))≤_
      rw [node_center,node_center]
      have hp := neighbors_in_ball hr q hnear p i
      have hs := neighbors_in_ball hr q hnear s i
      exact hcat.midpoint_lipschitz g hp.1 hp.2 hs.1 hs.2)
  refine ⟨p.val,p.property,fun i => ?_⟩
  have hh := congrArg (fun p : B => p.val (center i)) hp
  simpa only [T,node_center] using hh.symm

end LocalPolygonContinuation
end

section

/-! Constant-speed local geodesics and their genuine nearby uniqueness.
No covering, global comparison, or globalization conclusion is assumed. -/
open Set Metric
variable {X : Type*} [MetricSpace X]

lemma UniformLocalCATZero.eq_midpoint_of_dist {r : ℝ} (h : UniformLocalCATZero (X:=X) r)
    (g : IsGeodesic X) {o a b p : X}
    (ha : a ∈ ball o (r/3)) (hb : b ∈ ball o (r/3)) (hp : p ∈ ball o (r/3))
    (hpa : dist a p=dist a b/2) (hpb : dist p b=dist a b/2) : p=g.midpoint a b := by
  have hr : 0 < r := by rw [mem_ball] at ha; linarith [dist_nonneg (x:=a) (y:=o)]
  obtain ⟨U,hU,hcat⟩ := h o
  have sub : ball o (r/3) ⊆ U := (ball_subset_ball (by linarith)).trans hU
  have he : (⟨p,sub hp⟩ : U)=CATZero.mid hcat ⟨a,sub ha⟩ ⟨b,sub hb⟩ := by
    apply CATZero.eq_segment_of_dist hcat (by norm_num : (1/2:ℝ) ∈ Icc 0 1)
    · change dist a p=(1/2)*dist a b
      rw [hpa]; ring
    · change dist p b=(1-1/2)*dist a b
      rw [hpb]; ring
  have hm := midpoint_eq_subtype hcat g (sub ha) (sub hb) (hU (g.midpoint_mem_ball ha hb))
  exact congrArg Subtype.val (he.trans hm.symm)

lemma IsLocalSegment.close_chord {α β : ℝ → X} {A B r : ℝ}
    (hα : IsLocalSegment α A) (hβ : IsLocalSegment β B)
    (hr : 0 < r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
    (hclose : ∀ t ∈ Icc (0:ℝ) 1, dist (α t) (β t) < r/10) :
    ∀ t ∈ Icc (0:ℝ) 1, dist (α t) (β t)≤
      (1-t)*dist (α 0) (β 0)+t*dist (α 1) (β 1) := by
  obtain ⟨εa,hea,hda⟩ := hα.local_dist
  obtain ⟨εb,heb,hdb⟩ := hβ.local_dist
  let R := 1+A+B
  have hR : 0<R := by dsimp [R]; linarith [hα.nonneg,hβ.nonneg]
  let δ := min εa (min εb (r/(20*R)))
  have hδ : 0<δ := lt_min hea (lt_min heb (div_pos hr (by positivity)))
  apply CurvatureComparison.local_midpoint_chord (continuous_dist.comp_continuousOn (hα.continuousOn.prodMk hβ.continuousOn)) hδ
  intro s hs t ht hst
  let m := (s+t)/2
  have hm : m ∈ Icc (0:ℝ) 1 := ⟨by dsimp [m]; linarith [hs.1,ht.1],by dsimp [m]; linarith [hs.2,ht.2]⟩
  have hsm : |s-m|=|s-t|/2 := by rw [show s-m=(s-t)/2 by dsimp [m]; ring,abs_div]; norm_num
  have hmt : |m-t|=|s-t|/2 := by rw [show m-t=(s-t)/2 by dsimp [m]; ring,abs_div]; norm_num
  have hsta : |s-t|<εa := hst.trans_le (min_le_left _ _)
  have hstb : |s-t|<εb := hst.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hstr : |s-t| *R < r/20 := by
    have hh := hst.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hh' := (lt_div_iff₀ (by positivity : 0<20*R)).mp hh
    linarith
  have haa : |s-t| *A < r/20 := by
    have he : A≤R := by dsimp [R]; linarith [hβ.nonneg]
    nlinarith [mul_le_mul_of_nonneg_left he (abs_nonneg (s-t))]
  have hbb : |s-t| *B < r/20 := by
    have he : B≤R := by dsimp [R]; linarith [hα.nonneg]
    nlinarith [mul_le_mul_of_nonneg_left he (abs_nonneg (s-t))]
  have ha₁ : dist (α s) (α m)=|s-t|/2*A := by
    rw [hda s hs m hm (by rw [hsm]; linarith [abs_nonneg (s-t)]),hsm]
  have ha₂ : dist (α m) (α t)=|s-t|/2*A := by
    rw [hda m hm t ht (by rw [hmt]; linarith [abs_nonneg (s-t)]),hmt]
  have hb₁ : dist (β s) (β m)=|s-t|/2*B := by
    rw [hdb s hs m hm (by rw [hsm]; linarith [abs_nonneg (s-t)]),hsm]
  have hb₂ : dist (β m) (β t)=|s-t|/2*B := by
    rw [hdb m hm t ht (by rw [hmt]; linarith [abs_nonneg (s-t)]),hmt]
  have has : α s ∈ ball (α m) (r/3) := by rw [mem_ball,ha₁]; nlinarith [mul_nonneg (abs_nonneg (s-t)) hα.nonneg]
  have hat : α t ∈ ball (α m) (r/3) := by rw [mem_ball,dist_comm,ha₂]; nlinarith [mul_nonneg (abs_nonneg (s-t)) hα.nonneg]
  have hbs : β s ∈ ball (α m) (r/3) := by
    rw [mem_ball]
    have hh := dist_triangle (β s) (β m) (α m)
    rw [hb₁,dist_comm (β m) (α m)] at hh
    nlinarith [hclose m hm,mul_nonneg (abs_nonneg (s-t)) hβ.nonneg]
  have hbt : β t ∈ ball (α m) (r/3) := by
    rw [mem_ball]
    have hh := dist_triangle (β t) (β m) (α m)
    rw [dist_comm (β t) (β m),hb₂,dist_comm (β m) (α m)] at hh
    nlinarith [hclose m hm,mul_nonneg (abs_nonneg (s-t)) hβ.nonneg]
  have ham : α m ∈ ball (α m) (r/3) := mem_ball_self (by positivity)
  have hbm : β m ∈ ball (α m) (r/3) := by rw [mem_ball,dist_comm]; linarith [hclose m hm]
  have hemα : α m=g.midpoint (α s) (α t) := hc.eq_midpoint_of_dist g has hat ham
    (by rw [ha₁,hda s hs t ht hsta]; ring) (by rw [ha₂,hda s hs t ht hsta]; ring)
  have hemβ : β m=g.midpoint (β s) (β t) := hc.eq_midpoint_of_dist g hbs hbt hbm
    (by rw [hb₁,hdb s hs t ht hstb]; ring) (by rw [hb₂,hdb s hs t ht hstb]; ring)
  change dist (α m) (β m)≤_
  rw [hemα,hemβ]
  exact hc.midpoint_lipschitz g has hat hbs hbt

end

/-! Literal equal-time interpolation of finite geodesic polygons. -/
open Set Metric
namespace SegmentChain
variable {X : Type*} [MetricSpace X] {N : ℕ} (hN : 0 < N)

include hN

variable (p : ℕ → X) (γ : ℕ → ℝ → X)
  (hg : ∀ i, i < N → IsSegment (γ i) (p i) (p (i+1)))

include hg

lemma curve_eq (i : Fin N) {t : ℝ} (hi : t ∈ Icc (i:ℝ) ((i:ℝ)+1)) :
    curve hN p γ t=γ i (t-(i:ℝ)) := by
  have ht : t ∈ Icc (0:ℝ) N := by
    rw [←interval_union hN]
    exact mem_iUnion.mpr ⟨i,hi⟩
  rw [curve,dite_eq_left ht]
  exact compatible p γ hg (cell hN t ht) i (cell_mem hN t ht) hi

lemma curve_continuousOn : ContinuousOn (curve hN p γ) (Icc (0:ℝ) N) := by
  rw [←interval_union hN]
  apply (locallyFinite_of_finite (fun i : Fin N =>  Icc (i:ℝ) ((i:ℝ)+1))).continuousOn_iUnion
    (fun _ =>  isClosed_Icc)
  intro i
  have hh : ContinuousOn (fun t : ℝ =>  γ i (t-(i:ℝ))) (Icc (i:ℝ) ((i:ℝ)+1)) :=
    (hg i i.isLt).continuousOn.comp (continuous_id.sub continuous_const).continuousOn
      (fun t ht =>  ⟨by linarith [ht.1],by linarith [ht.2]⟩)
  apply hh.congr
  intro t ht
  exact curve_eq hN p γ hg i ht

lemma curve_zero : curve hN p γ 0=p 0 := by
  let i : Fin N := ⟨0,hN⟩
  rw [curve_eq hN p γ hg i (by simp [i])]
  simpa [i] using (hg 0 hN).1

lemma curve_last : curve hN p γ N=p N := by
  let i : Fin N := ⟨N-1,by omega⟩
  have he : (N-1:ℕ)+1=N := by omega
  have her : ((N-1:ℕ):ℝ)+1=N := by exact_mod_cast he
  have hi : (N:ℝ) ∈ Icc (i:ℝ) ((i:ℝ)+1) := by change (N-1:ℕ) ≤ (N:ℝ) ∧ (N:ℝ) ≤ (N-1:ℕ)+1; constructor  <;>  linarith
  rw [curve_eq hN p γ hg i hi]
  have harg : (N:ℝ)-(i:ℝ)=1 := by dsimp [i]; linarith
  rw [harg,(hg i i.isLt).2.1]
  exact congrArg p he

lemma unitCurve_continuousOn : ContinuousOn (unitCurve hN p γ) (Icc (0:ℝ) 1) := by
  apply (curve_continuousOn hN p γ hg).comp (continuous_const.mul continuous_id).continuousOn
  intro t ht
  change 0 ≤ (N:ℝ)*t ∧ (N:ℝ)*t ≤ N
  exact ⟨mul_nonneg (Nat.cast_nonneg _) ht.1,by nlinarith [(Nat.cast_pos.mpr hN : (0:ℝ) < N),ht.2]⟩

lemma unitCurve_zero : unitCurve hN p γ 0=p 0 := by simpa [unitCurve] using curve_zero hN p γ hg
lemma unitCurve_one : unitCurve hN p γ 1=p N := by simpa [unitCurve] using curve_last hN p γ hg

end SegmentChain

end HyperbolicObstruction

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LocalSegmentTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


noncomputable section
open Set Metric
namespace HyperbolicObstruction
variable {X : Type*} [MetricSpace X]

lemma IsLocalSegment.close_length {α β : ℝ → X} {A B r : ℝ}
    (hα : IsLocalSegment α A) (hβ : IsLocalSegment β B)
    (hr : 0 < r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
    (hclose : ∀ t ∈ Icc (0:ℝ) 1, dist (α t) (β t) < r/10)
    (h0 : α 0=β 0) : |A-B|≤dist (α 1) (β 1) := by
  obtain ⟨ε,hε,hd⟩ := hα.local_dist
  obtain ⟨δ,hδ,hd'⟩ := hβ.local_dist
  let t := min (1/2:ℝ) (min (ε/2) (δ/2))
  have ht : 0<t := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have ht1 : t≤1 := (min_le_left _ _).trans (by norm_num)
  have hte : t<ε := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
  have htd : t<δ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)
  have h0t : |(0:ℝ)-t|=t := by rw [zero_sub,abs_neg,abs_of_pos ht]
  have h1 := hd 0 (by norm_num) t ⟨ht.le,ht1⟩ (by rw [h0t]; exact hte)
  have h2 := hd' 0 (by norm_num) t ⟨ht.le,ht1⟩ (by rw [h0t]; exact htd)
  rw [h0t] at h1 h2
  have hh := abs_dist_sub_le (α t) (β t) (α 0)
  rw [dist_comm (α t) (α 0),dist_comm (β t) (α 0),h1,h0,h2] at hh
  have hc' := hα.close_chord hβ hr hc g hclose t ⟨ht.le,ht1⟩
  rw [h0,dist_self,mul_zero,zero_add] at hc'
  rw [←mul_sub,abs_mul,abs_of_pos ht] at hh
  exact (le_of_mul_le_mul_left (hh.trans hc') ht)

end HyperbolicObstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StationaryInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! A midpoint-stationary short polygon interpolates to an actual
constant-speed local geodesic, rather than merely to a combinatorial chain. -/
noncomputable section
open Set Metric
namespace HyperbolicObstruction
variable {X : Type*} [MetricSpace X]

lemma UniformLocalCATZero.segment_unique {r : ℝ} (hc : UniformLocalCATZero (X:=X) r)
    {a b : X} {α β : ℝ → X} (hα : IsSegment α a b) (hβ : IsSegment β a b)
    (hab : dist a b < r) : EqOn α β (Icc 0 1) := by
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg hab
  obtain ⟨U,hU,hcat⟩ := hc a
  have ha : a ∈ U := hU (mem_ball_self hr)
  have hb : b ∈ U := hU (by simpa [mem_ball,dist_comm] using hab)
  intro t ht
  have hmem {γ : ℝ → X} (hγ : IsSegment γ a b) : γ t ∈ U := by
    apply hU
    rw [mem_ball,dist_comm,hγ.dist_from_source ht]
    have hh : t*dist a b  ≤  dist a b := by nlinarith [ht.2,dist_nonneg (x:=a) (y:=b)]
    exact hh.trans_lt hab
  have he {γ : ℝ → X} (hγ : IsSegment γ a b) :
      (⟨γ t,hmem hγ⟩ : U)=CATZero.segment hcat ⟨a,ha⟩ ⟨b,hb⟩ t := by
    apply CATZero.eq_segment_of_dist hcat ht
    · exact hγ.dist_from_source ht
    · change dist (γ t) b=(1-t)*dist a b
      have hh := hγ.2.2 t ht 1 (by norm_num)
      rw [hγ.2.1,abs_of_nonpos (sub_nonpos.mpr ht.2)] at hh
      simpa only [neg_sub] using hh
  exact congrArg Subtype.val ((he hα).trans (he hβ).symm)

namespace StationaryInterpolation
variable (g : IsGeodesic X) {r : ℝ} (hc : UniformLocalCATZero (X:=X) r)
  {N : ℕ} (hN : 0 < N) (p : ℕ → X)
  (hshort : ∀ i, i < N → dist (p i) (p (i+1)) < r)
  (hmid : ∀ i, i+2 ≤ N → p (i+1)=g.midpoint (p i) (p (i+2)))

include hc hshort hmid in
lemma double_eq {i : ℕ} (hi : i+2 ≤ N) {t : ℝ} (ht : t ∈ Icc (i:ℝ) ((i:ℝ)+2)) :
    SegmentChain.curve hN p (edge g p) t = g.segment (p i) (p (i+2)) ((t-i)/2) := by
  let δ := g.segment (p i) (p (i+2))
  have hd : IsSegment δ (p i) (p (i+2)) := g.segment_spec _ _
  have hm : δ (1/2)=p (i+1) := (hmid i hi).symm
  have hzero : δ 0=p i := hd.1
  have hone : δ 1=p (i+2) := hd.2.1
  have hleft : IsSegment (fun u => δ (u/2)) (p i) (p (i+1)) := by
    have hh := hd.reparam (by norm_num : (0:ℝ) ∈ Icc 0 1) (by norm_num : (1/2:ℝ) ∈ Icc 0 1)
    simpa only [mul_zero,zero_add,mul_one_div,hzero,hm] using hh
  have hright : IsSegment (fun u => δ ((1+u)/2)) (p (i+1)) (p (i+2)) := by
    have hh := hd.reparam (by norm_num : (1/2:ℝ) ∈ Icc 0 1) (by norm_num : (1:ℝ) ∈ Icc 0 1)
    rw [hm,hone] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext u
    congr 1
    ring
  by_cases hle : t ≤ (i:ℝ)+1
  · let j : Fin N := ⟨i,by omega⟩
    have htj : t ∈ Icc (j:ℝ) ((j:ℝ)+1) := ⟨ht.1,hle⟩
    rw [SegmentChain.curve_eq hN p (edge g p) (fun k _ => edge_spec g p k) j htj]
    exact hc.segment_unique (edge_spec g p i) hleft (hshort i (by omega))
      ⟨by linarith [ht.1],by linarith⟩
  · let j : Fin N := ⟨i+1,by omega⟩
    have htj : t ∈ Icc (j:ℝ) ((j:ℝ)+1) := by
      change (i+1:ℕ) ≤ t ∧ t ≤ (i+1:ℕ)+1
      push_cast
      constructor <;> linarith [ht.2]
    rw [SegmentChain.curve_eq hN p (edge g p) (fun k _ => edge_spec g p k) j htj]
    have hh := hc.segment_unique (edge_spec g p (i+1)) hright (hshort (i+1) (by omega))
      (show t-(i+1:ℕ) ∈ Icc (0:ℝ) 1 from by push_cast; constructor <;> linarith [ht.2])
    change g.segment (p (i+1)) (p (i+1+1)) (t-(i+1:ℕ))=_ at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [δ]
    congr 1
    push_cast
    ring

include hc hshort hmid in
lemma curve_local_dist {s t : ℝ} (hs : s ∈ Icc (0:ℝ) N) (ht : t ∈ Icc (0:ℝ) N)
    (hst : |s-t| < 1) :
    dist (SegmentChain.curve hN p (edge g p) s) (SegmentChain.curve hN p (edge g p) t)=
      |s-t| * dist (p 0) (p 1) := by
  obtain ⟨i,hi⟩ := SegmentChain.interval_cover hN hs
  obtain ⟨j,hj⟩ := SegmentChain.interval_cover hN ht
  have same (k : Fin N) (hs' : s ∈ Icc (k:ℝ) ((k:ℝ)+1)) (ht' : t ∈ Icc (k:ℝ) ((k:ℝ)+1)) :
      dist (SegmentChain.curve hN p (edge g p) s) (SegmentChain.curve hN p (edge g p) t)=
        |s-t| * dist (p 0) (p 1) := by
    rw [SegmentChain.curve_eq hN p (edge g p) (fun k _ => edge_spec g p k) k hs',
      SegmentChain.curve_eq hN p (edge g p) (fun k _ => edge_spec g p k) k ht']
    rw [(edge_spec g p k).2.2 _ ⟨by linarith [hs'.1],by linarith [hs'.2]⟩
      _ ⟨by linarith [ht'.1],by linarith [ht'.2]⟩]
    rw [show s-(k:ℝ)-(t-(k:ℝ))=s-t by ring,edge_length_eq g p hmid k.isLt]
  have both (k : ℕ) (hk : k+2 ≤ N) (hs' : s ∈ Icc (k:ℝ) ((k:ℝ)+2))
      (ht' : t ∈ Icc (k:ℝ) ((k:ℝ)+2)) :
      dist (SegmentChain.curve hN p (edge g p) s) (SegmentChain.curve hN p (edge g p) t)=
        |s-t| * dist (p 0) (p 1) := by
    rw [double_eq g hc hN p hshort hmid hk hs',double_eq g hc hN p hshort hmid hk ht']
    rw [(g.segment_spec (p k) (p (k+2))).2.2 _ ⟨by linarith [hs'.1],by linarith [hs'.2]⟩
      _ ⟨by linarith [ht'.1],by linarith [ht'.2]⟩]
    have hd : dist (p k) (p (k+2))=2*dist (p 0) (p 1) := by
      have hh := g.dist_left_midpoint (p k) (p (k+2))
      rw [←hmid k hk,edge_length_eq g p hmid (by omega : k < N)] at hh
      linarith
    rw [hd,show (s-(k:ℝ))/2-(t-(k:ℝ))/2=(s-t)/2 by ring,abs_div]
    norm_num
    ring
  rcases lt_trichotomy i.val j.val with hlt|he|hgt
  · have hji : j.val=i.val+1 := by
      have hjr : (j:ℝ) < (i:ℝ)+2 := by have := (abs_lt.mp hst).1; linarith [hi.2,hj.1]
      have hjn : j.val < i.val+2 := by exact_mod_cast hjr
      omega
    apply both i (by have := j.isLt; omega) ⟨hi.1,by linarith [hi.2]⟩
    have hj1 := hj.1; have hj2 := hj.2
    change (j.val:ℝ) ≤ t at hj1
    change t ≤ (j.val:ℝ)+1 at hj2
    rw [hji] at hj1 hj2
    push_cast at hj1 hj2
    constructor <;> linarith
  · have hij : i=j := Fin.ext he
    subst j
    exact same i hi hj
  · have hij : i.val=j.val+1 := by
      have hir : (i:ℝ) < (j:ℝ)+2 := by have := (abs_lt.mp hst).2; linarith [hi.1,hj.2]
      have hin : i.val < j.val+2 := by exact_mod_cast hir
      omega
    apply both j (by have := i.isLt; omega) _ ⟨hj.1,by linarith [hj.2]⟩
    have hi1 := hi.1; have hi2 := hi.2
    change (i.val:ℝ) ≤ s at hi1
    change s ≤ (i.val:ℝ)+1 at hi2
    rw [hij] at hi1 hi2
    push_cast at hi1 hi2
    constructor <;> linarith

include hc hshort hmid in
lemma isLocalSegment :
    IsLocalSegment (SegmentChain.unitCurve hN p (edge g p)) ((N:ℝ)*dist (p 0) (p 1)) := by
  refine ⟨mul_nonneg (Nat.cast_nonneg _) dist_nonneg,
    SegmentChain.unitCurve_continuousOn hN p (edge g p) (fun k _ => edge_spec g p k),
    1/(N:ℝ),by positivity,?_⟩
  intro s hs t ht hst
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hin (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : (N:ℝ)*u ∈ Icc (0:ℝ) N :=
    ⟨mul_nonneg hn.le hu.1,by nlinarith [hu.2]⟩
  have hh : |(N:ℝ)*s-(N:ℝ)*t| < 1 := by
    rw [←mul_sub,abs_mul,abs_of_pos hn]
    have hh := (lt_div_iff₀ hn).mp hst
    nlinarith
  unfold SegmentChain.unitCurve
  rw [curve_local_dist g hc hN p hshort hmid (hin s hs) (hin t ht) hh,
    ←mul_sub,abs_mul,abs_of_pos hn]
  ring

end StationaryInterpolation
end HyperbolicObstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LocalSegmentContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


noncomputable section
open Set Metric
namespace HyperbolicObstruction
variable {X : Type*} [MetricSpace X] [CompactSpace X]

omit [CompactSpace X] in
lemma UniformLocalCATZero.mono {r s : ℝ} (h : UniformLocalCATZero (X:=X) r) (hs : s ≤ r) :
    UniformLocalCATZero (X:=X) s := fun x => by
  obtain ⟨U,hU,hcat⟩ := h x
  exact ⟨U,(ball_subset_ball hs).trans hU,hcat⟩

/-- Uniform endpoint continuation of every actual local metric geodesic. -/
theorem IsLocalSegment.continuation {α : ℝ → X} {A r : ℝ}
    (hα : IsLocalSegment α A) (hr : 0 < r) (hc : UniformLocalCATZero (X:=X) r)
    (g : IsGeodesic X) {a b : X} (ha : dist a (α 0) ≤ r/2000)
    (hb : dist b (α 1) ≤ r/2000) :
    ∃ β : ℝ → X, ∃ B : ℝ, IsLocalSegment β B ∧ β 0=a ∧ β 1=b ∧
      ∀ t ∈ Icc (0:ℝ) 1, dist (α t) (β t)≤
        (1-t)*dist (α 0) a+t*dist (α 1) b := by
  obtain ⟨ε,hε,hd⟩ := hα.local_dist
  obtain ⟨n,hn⟩ := exists_nat_gt (max (2/ε) (10000*(A+1)/r))
  let N := n+1
  have hN : 0<N := by dsimp [N]; omega
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hlarge : 2/ε<(N:ℝ) := by dsimp [N]; push_cast; linarith [(le_max_left (2/ε) (10000*(A+1)/r)).trans_lt hn]
  have he : 2/(N:ℝ)<ε := (div_lt_iff₀ hNr).mpr (by have := (div_lt_iff₀ hε).mp hlarge; nlinarith)
  have hA : A/(N:ℝ) < r/10000 := by
    have hh : 10000*(A+1)/r<(N:ℝ) := by dsimp [N]; push_cast; linarith [(le_max_right (2/ε) (10000*(A+1)/r)).trans_lt hn]
    have hh' := (div_lt_iff₀ hr).mp hh
    apply (div_lt_iff₀ hNr).mpr
    nlinarith
  let τ : ℕ → ℝ := fun i => (i:ℝ)/N
  have hτ (i : ℕ) (hi : i≤N) : τ i ∈ Icc (0:ℝ) 1 :=
    ⟨by dsimp [τ]; positivity,(div_le_one hNr).mpr (by exact_mod_cast hi)⟩
  have hτ0 : τ 0=0 := by simp [τ]
  have hτN : τ N=1 := by simp [τ,ne_of_gt hNr]
  have hτdiff (i j : ℕ) : |τ i-τ j|=|(i:ℝ)-(j:ℝ)|/N := by
    dsimp [τ]; rw [←sub_div,abs_div,abs_of_pos hNr]
  let q : Fin (n+2) → X := fun i => α (τ i)
  have hqd (i j : ℕ) (hi : i≤N) (hj : j≤N) (hij : |(i:ℝ)-(j:ℝ)|≤2) :
      dist (α (τ i)) (α (τ j))=(|(i:ℝ)-(j:ℝ)|/N)*A := by
    rw [hd _ (hτ i hi) _ (hτ j hj) (by rw [hτdiff]; exact (div_le_div_of_nonneg_right hij hNr.le).trans_lt he),hτdiff]
  have hstep (i : ℕ) (hi : i<N) : dist (α (τ i)) (α (τ (i+1)))=A/N := by
    rw [hqd i (i+1) (by omega) (by omega) (by push_cast; rw [show (i:ℝ)-((i:ℝ)+1)= -1 by ring]; norm_num)]
    push_cast
    rw [show (i:ℝ)-((i:ℝ)+1)= -1 by ring]
    norm_num; ring
  have hdouble (i : ℕ) (hi : i+2≤N) : dist (α (τ i)) (α (τ (i+2)))=2*A/N := by
    rw [hqd i (i+2) (by omega) hi (by push_cast; rw [show (i:ℝ)-((i:ℝ)+2)= -2 by ring]; norm_num)]
    push_cast
    rw [show (i:ℝ)-((i:ℝ)+2)= -2 by ring]
    norm_num; ring
  let ρ := r/100
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  have hcρ : UniformLocalCATZero (X:=X) ρ := hc.mono (by dsimp [ρ]; linarith)
  have hnear : ∀ i : Fin n,
      dist (q (FiniteMidpointFixedPoint.left i)) (q (FiniteMidpointFixedPoint.center i))<ρ/10 ∧
      dist (q (FiniteMidpointFixedPoint.right i)) (q (FiniteMidpointFixedPoint.center i))<ρ/10 := by
    intro i
    change dist (α (τ i)) (α (τ (i.val+1)))<ρ/10 ∧ dist (α (τ (i.val+2))) (α (τ (i.val+1)))<ρ/10
    rw [hstep i (by dsimp [N]; omega),dist_comm (α (τ (i.val+2))),show i.val+2=(i.val+1)+1 by omega,
      hstep (i.val+1) (by dsimp [N]; have := i.isLt; omega)]
    dsimp [ρ]; constructor <;> linarith
  have hmid : ∀ i : Fin n, q (FiniteMidpointFixedPoint.center i)=
      g.midpoint (q (FiniteMidpointFixedPoint.left i)) (q (FiniteMidpointFixedPoint.right i)) := by
    intro i
    change α (τ (i.val+1))=g.midpoint (α (τ i)) (α (τ (i.val+2)))
    have hi : i.val+2≤N := by dsimp [N]; have := i.isLt; omega
    have h0 := hstep i (by omega)
    have h1 := hstep (i.val+1) (by omega)
    have h2 := hdouble i hi
    apply hcρ.eq_midpoint_of_dist g (o:=α (τ (i.val+1)))
    · rw [mem_ball,h0]; dsimp [ρ]; linarith
    · rw [mem_ball,dist_comm]; change dist (α (τ (i.val+1))) (α (τ ((i.val+1)+1)))<ρ/3
      rw [h1]; dsimp [ρ]; linarith
    · exact mem_ball_self (by positivity)
    · rw [h0,h2]; ring
    · change dist (α (τ (i.val+1))) (α (τ ((i.val+1)+1)))=_
      rw [h1,h2]; ring
  obtain ⟨p,hp,hpm⟩ := LocalPolygonContinuation.exists_stationary hρ hcρ g q hnear hmid
    (a:=a) (b:=b) (by change dist a (α (τ 0))≤ρ/20; rw [hτ0]; dsimp [ρ]; linarith)
    (by change dist b (α (τ N))≤ρ/20; rw [hτN]; dsimp [ρ]; linarith)
  let P : ℕ → X := fun i => p ⟨min i N,by dsimp [N]; omega⟩
  have hP (i : ℕ) (hi : i≤N) : P i=p ⟨i,by dsimp [N] at hi; omega⟩ := by
    dsimp [P]; congr; exact min_eq_left hi
  have hcloseP (i : ℕ) (hi : i≤N) : dist (P i) (α (τ i)) ≤ r/2000 := by
    rw [hP i hi]
    have hh := hp.2.2 (⟨i,by dsimp [N] at hi; omega⟩ : Fin (n+2))
    change dist (p ⟨i,_⟩) (α (τ i))≤ρ/20 at hh
    dsimp [ρ] at hh; linarith
  have hshort (i : ℕ) (hi : i<N) : dist (P i) (P (i+1)) < r/500 := by
    have hh := dist_triangle4 (P i) (α (τ i)) (α (τ (i+1))) (P (i+1))
    rw [hstep i hi,dist_comm (α (τ (i+1)))] at hh
    linarith [hcloseP i (by omega),hcloseP (i+1) (by omega)]
  have hpm' (i : ℕ) (hi : i+2≤N) : P (i+1)=g.midpoint (P i) (P (i+2)) := by
    rw [hP (i+1) (by omega),hP i (by omega),hP (i+2) hi]
    exact hpm ⟨i,by dsimp [N] at hi; omega⟩
  let β := SegmentChain.unitCurve hN P (StationaryInterpolation.edge g P)
  have hβ : IsLocalSegment β ((N:ℝ)*dist (P 0) (P 1)) :=
    StationaryInterpolation.isLocalSegment g hc hN P (fun i hi => (hshort i hi).trans (by linarith)) hpm'
  have hβ0 : β 0=a := by
    dsimp only [β]
    rw [SegmentChain.unitCurve_zero hN P _ (fun i _ => StationaryInterpolation.edge_spec g P i),hP 0 (by omega)]
    exact hp.1
  have hβ1 : β 1=b := by
    dsimp only [β]
    rw [SegmentChain.unitCurve_one hN P _ (fun i _ => StationaryInterpolation.edge_spec g P i),hP N le_rfl]
    exact hp.2.1
  have hclose : ∀ t ∈ Icc (0:ℝ) 1, dist (α t) (β t) < r/10 := by
    intro t ht
    have hNt : (N:ℝ)*t ∈ Icc (0:ℝ) N := ⟨mul_nonneg hNr.le ht.1,by nlinarith [ht.2]⟩
    obtain ⟨i,hi⟩ := SegmentChain.interval_cover hN hNt
    have hai : |t-τ i|≤1/(N:ℝ) := by
      apply (le_div_iff₀ hNr).mpr
      calc
        |t-τ i| *(N:ℝ)=|(t-τ i)*(N:ℝ)| := by rw [abs_mul,abs_of_pos hNr]
        _=|(N:ℝ)*t-(i:ℝ)| := by congr 1; dsimp [τ]; field_simp
        _≤1 := abs_le.mpr ⟨by linarith [hi.1],by linarith [hi.2]⟩
    have had : dist (α t) (α (τ i))≤A/N := by
      have hh := hα.dist_le ht (hτ i (Nat.le_of_lt i.isLt))
      apply hh.trans
      convert mul_le_mul_of_nonneg_right hai hα.nonneg using 1 <;> first | rfl | ring
    have hbp : dist (P i) (β t)≤dist (P i) (P (i.val+1)) := by
      change dist (P i) (SegmentChain.curve hN P (StationaryInterpolation.edge g P) ((N:ℝ)*t))≤_
      rw [SegmentChain.curve_eq hN P _ (fun i _ => StationaryInterpolation.edge_spec g P i) i hi,
        (StationaryInterpolation.edge_spec g P i).dist_from_source ⟨by linarith [hi.1],by linarith [hi.2]⟩]
      nlinarith [dist_nonneg (x:=P i) (y:=P (i.val+1)),hi.1,hi.2]
    have hh := dist_triangle4 (α t) (α (τ i)) (P i) (β t)
    rw [dist_comm (α (τ i)) (P i)] at hh
    linarith [hcloseP i (Nat.le_of_lt i.isLt),hshort i i.isLt]
  refine ⟨β,_,hβ,hβ0,hβ1,?_⟩
  intro t ht
  simpa only [hβ0,hβ1] using hα.close_chord hβ hr hc g hclose t ht

end HyperbolicObstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LocalGeodesicCover
attribute [-instance] _root_.OAI.HyperbolicObstruction.LocalGeodesic.instContractibleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! The space of genuine local geodesics based at a point, with its uniform
function-space topology. The endpoint map is a produced covering map. -/
noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction
variable {X : Type*} [MetricSpace X]

namespace LocalGeodesic
variable {o : X}

lemma close_isometry {r : ℝ} (hr : 0 < r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
    {a b : LocalGeodesic o} (hab : dist a b < r/10) : dist (endpoint a) (endpoint b)=dist a b := by
  apply le_antisymm (by simpa only [NNReal.coe_one,one_mul] using endpoint_lipschitz.dist_le_mul a b)
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro t
  have hh := a.localSegment.close_chord b.localSegment hr hc g
    (fun u hu => by rw [extend_mem _ hu,extend_mem _ hu]; exact (ContinuousMap.dist_apply_le_dist (⟨u,hu⟩:I)).trans_lt hab) t t.property
  simp only [extend_coe,extend_zero,extend_one,a.start,b.start,dist_self,mul_zero,zero_add] at hh
  exact hh.trans (by change (t:ℝ)*dist (a 1) (b 1)≤dist (a 1) (b 1); nlinarith [t.property.2,dist_nonneg (x:=a 1) (y:=b 1)])

variable [CompactSpace X]
lemma short_lift {r : ℝ} (hr : 0 < r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
    (a : LocalGeodesic o) (y : X) (hy : dist y (endpoint a) < r/2000) :
    ∃ b : LocalGeodesic o, endpoint b=y ∧ dist b a=dist y (endpoint a) := by
  obtain ⟨β,B,hβ,hβ0,hβ1,hclose⟩ := a.localSegment.continuation hr hc g
    (a:=o) (b:=y) (by rw [extend_zero,a.start,dist_self]; positivity) (by simpa [endpoint] using hy.le)
  let b : LocalGeodesic o := ofReal hβ hβ0
  have hb1 : endpoint b=y := hβ1
  have hba : dist b a≤dist y (endpoint a) := by
    apply (ContinuousMap.dist_le dist_nonneg).mpr
    intro t
    have hh := hclose t t.property
    simp only [extend_coe,extend_zero,extend_one,a.start,dist_self,mul_zero,zero_add] at hh
    change dist (β t) (a t)≤_
    rw [dist_comm]
    apply hh.trans
    rw [dist_comm (a 1) y]
    change (t:ℝ)*dist y (a 1)≤dist y (a 1)
    nlinarith [t.property.2,dist_nonneg (x:=y) (y:=a 1)]
  refine ⟨b,hb1,le_antisymm hba ?_⟩
  rw [←hb1]
  exact by simpa using endpoint_lipschitz.dist_le_mul b a

lemma coverData {r : ℝ} (hr : 0 < r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X) :
    UniformMetricCoverData (@endpoint X _ o) (r/2000) := by
  refine ⟨by positivity,fun a b hab => close_isometry hr hc g (by linarith),short_lift hr hc g⟩

lemma isCoveringMap {r : ℝ} (hr : 0 < r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X) :
    IsCoveringMap (@endpoint X _ o) := (coverData hr hc g).isCoveringMap

end LocalGeodesic
end HyperbolicObstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LocalGeodesicLength
attribute [-instance] _root_.OAI.HyperbolicObstruction.LocalGeodesic.instContractibleSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction
variable {X : Type*} [MetricSpace X]

namespace LocalGeodesic
variable {o : X} {r : ℝ} (hr : 0 < r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)

include hr hc g

lemma close_length {a b : LocalGeodesic o} (hab : dist a b < r/10) :
    |a.length-b.length|≤dist (endpoint a) (endpoint b) := by
  suffices hh : |a.length-b.length|≤dist (extend a.val 1) (extend b.val 1) by
    simpa only [extend_one,endpoint] using hh
  apply a.localSegment.close_length b.localSegment hr hc g
  · intro t ht
    rw [extend_mem _ ht,extend_mem _ ht]
    exact (ContinuousMap.dist_apply_le_dist (⟨t,ht⟩:I)).trans_lt hab
  · simp only [extend_zero,a.start,b.start]

lemma length_variation {α : ℝ → X} {A : ℝ} (hα : IsLocalSegment α A)
    (ρ : C(I,LocalGeodesic o)) (hp : ∀ t : I, endpoint (ρ t)=α t) (s t : I) :
    |(ρ s).length-(ρ t).length|≤|(s:ℝ)-t| *A := by
  obtain ⟨ε,hε,he⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous ρ.continuous) (r/10) (by positivity)
  have hh := @local_dist_le_global ℝ _ (fun u => (ρ (projIcc 0 1 zero_le_one u)).length) A ε hε
    (by intro u hu v hv huv
        rw [projIcc_of_mem zero_le_one hu,projIcc_of_mem zero_le_one hv,Real.dist_eq]
        apply (close_length hr hc g (he (by simpa [Subtype.dist_eq,Real.dist_eq] using huv))).trans
        rw [hp,hp]
        exact hα.dist_le hu hv) (s:=s) (t:=t) s.property t.property
  simpa only [projIcc_of_mem zero_le_one s.property,projIcc_of_mem zero_le_one t.property,Real.dist_eq] using hh

end LocalGeodesic
end HyperbolicObstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LocalGeodesicTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction
variable {E X : Type*} [MetricSpace E] [MetricSpace X]

namespace LocalGeodesic
variable [CompactSpace X] {o : X} {r : ℝ} (hr : 0 < r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)

include hr hc g in
lemma locallyPathConnected : LocallyPathConnectedSpace (LocalGeodesic o) :=
  (coverData hr hc g).locallyPathConnected g

end LocalGeodesic
end HyperbolicObstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LocalGeodesicRebase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction.LocalGeodesic
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable {r : ℝ} (hr : 0 < r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
variable {o q : X}

def basedLift (a : LocalGeodesic o) (b : LocalGeodesic q) (he : endpoint b=endpoint a) :
    C(LocalGeodesic o,LocalGeodesic q) := by
  letI := locallyPathConnected (o:=o) hr hc g
  exact ((isCoveringMap (o:=q) hr hc g).existsUnique_continuousMap_lifts
    ⟨endpoint,endpoint_continuous⟩ a b he).choose

lemma basedLift_start (a : LocalGeodesic o) (b : LocalGeodesic q) (he : endpoint b=endpoint a) :
    basedLift hr hc g a b he a=b := by
  let := locallyPathConnected (o:=o) hr hc g
  exact ((isCoveringMap (o:=q) hr hc g).existsUnique_continuousMap_lifts
    ⟨endpoint,endpoint_continuous⟩ a b he).choose_spec.1.1

lemma basedLift_endpoint (a : LocalGeodesic o) (b : LocalGeodesic q) (he : endpoint b=endpoint a)
    (z : LocalGeodesic o) : endpoint (basedLift hr hc g a b he z)=endpoint z := by
  let := locallyPathConnected (o:=o) hr hc g
  exact congrFun (((isCoveringMap (o:=q) hr hc g).existsUnique_continuousMap_lifts
    ⟨endpoint,endpoint_continuous⟩ a b he).choose_spec.1.2) z

lemma basedLift_inv (a : LocalGeodesic o) (b : LocalGeodesic q) (he : endpoint b=endpoint a)
    (z : LocalGeodesic o) :
    basedLift hr hc g b a he.symm (basedLift hr hc g a b he z)=z := by
  have hh := (isCoveringMap (o:=o) hr hc g).eq_of_comp_eq
    ((basedLift hr hc g b a he.symm).continuous.comp (basedLift hr hc g a b he).continuous)
    continuous_id (by funext w; simp only [Function.comp_apply,basedLift_endpoint,id_eq]) a
    (by rw [Function.comp_apply,basedLift_start,basedLift_start]; rfl)
  exact congrFun hh z

/-- Re-basing changes the genuine local-geodesic model by a covering isomorphism. -/
def basedHomeomorph (a : LocalGeodesic o) (b : LocalGeodesic q) (he : endpoint b=endpoint a) :
    LocalGeodesic o ≃ₜ LocalGeodesic q where
  toFun := basedLift hr hc g a b he
  invFun := basedLift hr hc g b a he.symm
  left_inv := basedLift_inv hr hc g a b he
  right_inv := basedLift_inv hr hc g b a he.symm
  continuous_toFun := (basedLift hr hc g a b he).continuous
  continuous_invFun := (basedLift hr hc g b a he.symm).continuous

def rebase (a : LocalGeodesic o) : LocalGeodesic (endpoint a) ≃ₜ LocalGeodesic o :=
  basedHomeomorph hr hc g (constant (endpoint a)) a rfl

@[simp] lemma rebase_start (a : LocalGeodesic o) : rebase hr hc g a (constant (endpoint a))=a :=
  basedLift_start hr hc g _ _ _
@[simp] lemma rebase_endpoint (a : LocalGeodesic o) (b : LocalGeodesic (endpoint a)) :
    endpoint (rebase hr hc g a b)=endpoint b := basedLift_endpoint hr hc g _ _ _ _
@[simp] lemma rebase_symm_endpoint (a b : LocalGeodesic o) :
    endpoint ((rebase hr hc g a).symm b)=endpoint b := basedLift_endpoint hr hc g _ _ _ _
@[simp] lemma rebase_symm_self (a : LocalGeodesic o) : (rebase hr hc g a).symm a=constant (endpoint a) :=
  (Homeomorph.symm_apply_eq _).mpr (rebase_start hr hc g a).symm

end HyperbolicObstruction.LocalGeodesic
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LocalGeodesicDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction.LocalGeodesic
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable {r : ℝ} (hr : 0 < r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
variable {o : X}

omit [CompactSpace X] in
@[simp] lemma constant_length (x : X) : (constant x).length=0 := ofReal_length _ _

omit [CompactSpace X] in
lemma eq_constant_of_length_zero {a : LocalGeodesic o} (ha : a.length=0) : a=constant o := by
  ext t
  have hh:=a.localSegment.dist_le t.property (show (0:ℝ) ∈ Icc 0 1 by norm_num)
  simp only [extend_coe,extend_zero,a.start,ha,mul_zero] at hh
  exact dist_eq_zero.mp (le_antisymm hh dist_nonneg)

def joining (a b : LocalGeodesic o) : C(I,LocalGeodesic o) :=
  ⟨fun t => rebase hr hc g a (initial t ((rebase hr hc g a).symm b)),
    (rebase hr hc g a).continuous.comp (prefix_continuous.comp (continuous_id.prodMk continuous_const))⟩

@[simp] lemma joining_zero (a b : LocalGeodesic o) : joining hr hc g a b 0=a := by
  simp [joining]
@[simp] lemma joining_one (a b : LocalGeodesic o) : joining hr hc g a b 1=b := by
  simp [joining]
@[simp] lemma joining_endpoint (a b : LocalGeodesic o) (t : I) :
    endpoint (joining hr hc g a b t)=((rebase hr hc g a).symm b) t := by
  simp [joining]

def intrinsicDist (a b : LocalGeodesic o) : ℝ := ((rebase hr hc g a).symm b).length
lemma intrinsicDist_nonneg (a b : LocalGeodesic o) : 0≤ intrinsicDist hr hc g a b := length_nonneg _
@[simp] lemma intrinsicDist_self (a : LocalGeodesic o) : intrinsicDist hr hc g a a=0 := by simp [intrinsicDist]
lemma intrinsicDist_eq_zero {a b : LocalGeodesic o} (h : intrinsicDist hr hc g a b=0) : a=b := by
  have hh := eq_constant_of_length_zero h
  have hh' := congrArg (rebase hr hc g a) hh
  simpa using hh'.symm

lemma intrinsicDist_variation (x a b : LocalGeodesic o) :
    |intrinsicDist hr hc g x a-intrinsicDist hr hc g x b|≤ intrinsicDist hr hc g a b := by
  let c := (rebase hr hc g a).symm b
  let ρ : C(I,LocalGeodesic (endpoint x)) := (⟨(rebase hr hc g x).symm,(rebase hr hc g x).symm.continuous⟩ : C(_, _)).comp (joining hr hc g a b)
  have hh := length_variation hr hc g c.localSegment ρ
    (fun t => by simp [ρ,c]) 0 1
  simpa [ρ,intrinsicDist,c] using hh

lemma intrinsicDist_comm (a b : LocalGeodesic o) : intrinsicDist hr hc g a b=intrinsicDist hr hc g b a := by
  apply le_antisymm
  · have hh := intrinsicDist_variation hr hc g a b a
    simpa [abs_of_nonneg (intrinsicDist_nonneg hr hc g a b)] using hh
  · have hh := intrinsicDist_variation hr hc g b a b
    simpa [abs_of_nonneg (intrinsicDist_nonneg hr hc g b a)] using hh
lemma intrinsicDist_triangle (a b c : LocalGeodesic o) :
    intrinsicDist hr hc g a c≤ intrinsicDist hr hc g a b+intrinsicDist hr hc g b c := by
  have hh := intrinsicDist_variation hr hc g a c b
  rw [intrinsicDist_comm hr hc g c b] at hh
  have hle := (abs_le.mp hh).2
  linarith

lemma ordinary_dist_le_intrinsic (a b : LocalGeodesic o) : dist a b≤ intrinsicDist hr hc g a b := by
  let c := (rebase hr hc g a).symm b
  let ρ := joining hr hc g a b
  obtain ⟨ε,hε,he⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous ρ.continuous) (r/10) (by positivity)
  have hh := @local_dist_le_global (LocalGeodesic o) _ (fun u => ρ (projIcc 0 1 zero_le_one u)) c.length ε hε
    (by intro u hu v hv huv
        rw [projIcc_of_mem zero_le_one hu,projIcc_of_mem zero_le_one hv]
        rw [←close_isometry hr hc g (he (by simpa [Subtype.dist_eq,Real.dist_eq] using huv))]
        simp only [ρ,joining_endpoint]
        have hh:=c.localSegment.dist_le hu hv
        simpa only [extend_mem _ hu,extend_mem _ hv] using hh)
    (s:=0) (t:=1) (by norm_num) (by norm_num)
  simpa [ρ,c,intrinsicDist] using hh

end HyperbolicObstruction.LocalGeodesic
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ShortSegmentLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction
variable {E X : Type*} [MetricSpace E] [MetricSpace X]

lemma UniformMetricCoverData.shortSegmentLift {p : E → X} {r : ℝ}
    (h : UniformMetricCoverData p r) (g : IsGeodesic X)
    {a b : E} (hab : dist a b < r/4) :
    ∃ ρ : C(I,E), ρ 0=a ∧ ρ 1=b ∧ ∀ t : I, p (ρ t)=g.segment (p a) (p b) t := by
  have hpab : dist (p a) (p b)=dist a b := h.local_dist a b (by linarith [h.positive])
  let γ:=g.segment (p a) (p b)
  have hγ:=g.segment_spec (p a) (p b)
  have hm (t : I) : γ t ∈ ball (p a) (r/4) := by
    rw [mem_ball,dist_comm,hγ.dist_from_source t.property,hpab]
    have hh : (t:ℝ)*dist a b≤dist a b := by nlinarith [t.property.2,dist_nonneg (x:=a) (y:=b)]
    exact hh.trans_lt hab
  let f : I → E := fun t => (h.out (p a) ⟨a,rfl⟩ ⟨γ t,hm t⟩).val
  have hf : Continuous f := continuous_subtype_val.comp ((h.out_isometry (p a) ⟨a,rfl⟩).continuous.comp
    ((continuousOn_iff_continuous_domRestrict.mp hγ.continuousOn).subtype_mk hm))
  have hd (t : I) : dist (f t) a=(t:ℝ)*dist a b := by
    rw [show dist (f t) a=dist (γ t) (p a) from h.out_dist _ _ _,dist_comm,hγ.dist_from_source t.property,hpab]
  have h0 : f 0=a := by apply dist_eq_zero.mp; rw [hd]; simp
  have h1 : f 1=b := by
    apply h.nearby_unique
    · have hh:=dist_triangle (f 1) a b
      rw [hd] at hh
      norm_num at hh
      linarith [h.positive]
    · exact (h.out_proj _ _ _).trans hγ.2.1
  exact ⟨⟨f,hf⟩,h0,h1,fun t => h.out_proj _ _ _⟩

namespace LocalGeodesic
variable [CompactSpace X] {r : ℝ} (hr : 0 < r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
variable {o : X}

lemma intrinsicDist_eq_of_close {a b : LocalGeodesic o} (hab : dist a b < r/8000) :
    intrinsicDist hr hc g a b=dist a b := by
  apply le_antisymm _ (ordinary_dist_le_intrinsic hr hc g a b)
  obtain ⟨ρ,h0,h1,hp⟩ := (coverData hr hc g).shortSegmentLift g (by linarith : dist a b<(r/2000)/4)
  let rho2 : C(I,LocalGeodesic (endpoint a)) := (⟨(rebase hr hc g a).symm,(rebase hr hc g a).symm.continuous⟩ : C(_, _)).comp ρ
  have hh := length_variation hr hc g (g.segment_spec (endpoint a) (endpoint b)).isLocalSegment rho2
    (fun t => by change endpoint ((rebase hr hc g a).symm (ρ t))=_; rw [rebase_symm_endpoint]; exact hp t) 0 1
  have hh' : intrinsicDist hr hc g a b≤dist (endpoint a) (endpoint b) := by
    simpa [rho2,h0,h1,intrinsicDist,abs_of_nonneg (length_nonneg _)] using hh
  exact hh'.trans (by simpa using endpoint_lipschitz.dist_le_mul a b)

@[instance_reducible] def intrinsicMetric : MetricSpace (LocalGeodesic o) :=
  MetricSpace.ofDistTopology (intrinsicDist hr hc g) (intrinsicDist_self hr hc g)
    (intrinsicDist_comm hr hc g) (intrinsicDist_triangle hr hc g)
    (by intro s
        rw [Metric.isOpen_iff]
        constructor
        · intro hs a ha
          obtain ⟨ε,hε,he⟩:=hs a ha
          exact ⟨ε,hε,fun b hb => he (by rw [mem_ball,dist_comm]; exact (ordinary_dist_le_intrinsic hr hc g a b).trans_lt hb)⟩
        · intro hs a ha
          obtain ⟨ε,hε,he⟩:=hs a ha
          refine ⟨min ε (r/8000),lt_min hε (by positivity),fun b hb => ?_⟩
          have hb' : dist a b< min ε (r/8000) := by simpa [mem_ball,dist_comm] using hb
          apply he b
          rw [intrinsicDist_eq_of_close hr hc g (lt_min_iff.mp hb').2]
          exact (lt_min_iff.mp hb').1)
    (fun _ _ => intrinsicDist_eq_zero hr hc g)

end LocalGeodesic
end HyperbolicObstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_DevelopmentGeodesic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction.LocalGeodesic
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable {r : ℝ} (hr : 0 < r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
variable {o : X}

lemma joining_length_variation (x a b : LocalGeodesic o) (s t : I) :
    |intrinsicDist hr hc g x (joining hr hc g a b s)-intrinsicDist hr hc g x (joining hr hc g a b t)|≤
      |(s:ℝ)-t| *intrinsicDist hr hc g a b := by
  let c := (rebase hr hc g a).symm b
  let rho2 : C(I,LocalGeodesic (endpoint x)) :=
    (⟨(rebase hr hc g x).symm,(rebase hr hc g x).symm.continuous⟩ : C(_,_)).comp (joining hr hc g a b)
  have hh := length_variation hr hc g c.localSegment rho2 (fun t => by simp [rho2,c]) s t
  exact hh

lemma intrinsicDist_joining_le (a b : LocalGeodesic o) (s t : I) :
    intrinsicDist hr hc g (joining hr hc g a b s) (joining hr hc g a b t)≤
      |(s:ℝ)-t| *intrinsicDist hr hc g a b := by
  have hh := joining_length_variation hr hc g (joining hr hc g a b s) a b s t
  simpa only [intrinsicDist_self,zero_sub,abs_neg,abs_of_nonneg (intrinsicDist_nonneg hr hc g _ _)] using hh

lemma intrinsicDist_to_joining (a b : LocalGeodesic o) (t : I) :
    intrinsicDist hr hc g a (joining hr hc g a b t)=(t:ℝ)*intrinsicDist hr hc g a b := by
  simp [intrinsicDist,joining]

lemma intrinsicDist_joining (a b : LocalGeodesic o) (s t : I) :
    intrinsicDist hr hc g (joining hr hc g a b s) (joining hr hc g a b t)=
      |(s:ℝ)-t| *intrinsicDist hr hc g a b := by
  apply le_antisymm (intrinsicDist_joining_le hr hc g a b s t)
  have hh := intrinsicDist_variation hr hc g a (joining hr hc g a b s) (joining hr hc g a b t)
  rw [intrinsicDist_to_joining,intrinsicDist_to_joining,←sub_mul,abs_mul,abs_of_nonneg (intrinsicDist_nonneg hr hc g a b)] at hh
  exact hh

def developedSegment (a b : LocalGeodesic o) (t : ℝ) : LocalGeodesic o :=
  joining hr hc g a b (projIcc 0 1 zero_le_one t)

lemma developedSegment_spec (a b : LocalGeodesic o) :
    @IsSegment (LocalGeodesic o) (intrinsicMetric hr hc g) (developedSegment hr hc g a b) a b := by
  refine ⟨by simp [developedSegment],by simp [developedSegment],?_⟩
  intro s hs t ht
  change intrinsicDist hr hc g (developedSegment hr hc g a b s) (developedSegment hr hc g a b t)=|s-t| *intrinsicDist hr hc g a b
  simp only [developedSegment,projIcc_of_mem zero_le_one hs,projIcc_of_mem zero_le_one ht]
  exact intrinsicDist_joining hr hc g a b ⟨s,hs⟩ ⟨t,ht⟩

lemma developed_isGeodesic : @IsGeodesic (LocalGeodesic o) (intrinsicMetric hr hc g) :=
  fun a b => ⟨developedSegment hr hc g a b,developedSegment_spec hr hc g a b⟩

end HyperbolicObstruction.LocalGeodesic
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_DevelopmentRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction.LocalGeodesic
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable {r : ℝ} (hr : 0 < r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
variable {o q : X}

lemma intrinsicDist_map_le (F : C(LocalGeodesic o,LocalGeodesic q))
    (hp : ∀ a, endpoint (F a)=endpoint a) (a b : LocalGeodesic o) :
    intrinsicDist hr hc g (F a) (F b)≤ intrinsicDist hr hc g a b := by
  let c := (rebase hr hc g a).symm b
  let rho2 : C(I,LocalGeodesic (endpoint (F a))) :=
    (⟨(rebase hr hc g (F a)).symm,(rebase hr hc g (F a)).symm.continuous⟩ : C(_,_)).comp
      (F.comp (joining hr hc g a b))
  have hh := length_variation hr hc g c.localSegment rho2
    (fun t => by change endpoint ((rebase hr hc g (F a)).symm (F (joining hr hc g a b t)))=extend c.val t
                 rw [rebase_symm_endpoint,hp,joining_endpoint,extend_coe]) 0 1
  simpa [rho2,c,intrinsicDist,abs_of_nonneg (length_nonneg _)] using hh

lemma intrinsicDist_homeomorph (F : LocalGeodesic o ≃ₜ LocalGeodesic q)
    (hp : ∀ a, endpoint (F a)=endpoint a) (a b : LocalGeodesic o) :
    intrinsicDist hr hc g (F a) (F b)=intrinsicDist hr hc g a b := by
  apply le_antisymm (intrinsicDist_map_le hr hc g ⟨F,F.continuous⟩ hp a b)
  have hpinv : ∀ z, endpoint (F.symm z)=endpoint z := fun z => by simpa using (hp (F.symm z)).symm
  simpa using intrinsicDist_map_le hr hc g ⟨F.symm,F.symm.continuous⟩ hpinv (F a) (F b)

end HyperbolicObstruction.LocalGeodesic
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_DevelopmentDeck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction.LocalGeodesic
variable {X : Type*} [MetricSpace X]

def deckSubgroup (o : X) : Subgroup (LocalGeodesic o ≃ₜ LocalGeodesic o) where
  carrier := {f | ∀ a, endpoint (f a)=endpoint a}
  one_mem' := fun _ => rfl
  mul_mem' hf hg a := (hf _).trans (hg a)
  inv_mem' := by
    intro f hf a
    change endpoint (f.symm a)=endpoint a
    have hh:=hf (f.symm a)
    rw [Homeomorph.apply_symm_apply] at hh
    exact hh.symm

abbrev Deck (o : X) := deckSubgroup o

instance instMulActionSubtypeHomeomorphMemSubgroupDeck (o : X) : MulAction (Deck o) (LocalGeodesic o) where
  smul d a := d.val a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] lemma deck_endpoint {o : X} (d : Deck o) (a : LocalGeodesic o) : endpoint (d • a)=endpoint a := d.property a
instance instContinuousConstSMulSubtypeHomeomorphMemSubgroupDeck {o : X} : ContinuousConstSMul (Deck o) (LocalGeodesic o) where
  continuous_const_smul d := d.val.continuous

variable [CompactSpace X] {r : ℝ} (hr : 0 < r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
variable {o : X}
include hr hc g
lemma deck_ext {d e : Deck o} (a : LocalGeodesic o) (h : d • a=e • a) : d=e := by
  apply Subtype.ext
  apply Homeomorph.ext
  exact congrFun ((isCoveringMap hr hc g).eq_of_comp_eq d.val.continuous e.val.continuous
    (by funext z; exact (d.property z).trans (e.property z).symm) a h)

lemma deck_exists (a b : LocalGeodesic o) (h : endpoint b=endpoint a) : ∃ d : Deck o, d • a=b := by
  exact ⟨⟨basedHomeomorph hr hc g a b h,fun z => basedLift_endpoint hr hc g a b h z⟩,
    basedLift_start hr hc g a b h⟩

omit [CompactSpace X] hr hc in
lemma endpoint_surjective : Function.Surjective (@endpoint X _ o) := by
  intro y
  exact ⟨ofReal (g.segment_spec o y).isLocalSegment (g.segment_spec o y).1,(g.segment_spec o y).2.1⟩

lemma deck_quotientCovering : IsQuotientCoveringMap (@endpoint X _ o) (Deck o) where
  toIsQuotientMap := (isCoveringMap hr hc g).isQuotientMap (endpoint_surjective g)
  continuous_const_smul d := continuous_const_smul d
  apply_eq_iff_mem_orbit := by
    intro a b
    constructor
    · intro hh
      obtain ⟨d,hd⟩:=deck_exists hr hc g b a hh
      exact ⟨d,hd⟩
    · rintro ⟨d,rfl⟩
      exact deck_endpoint d b
  disjoint a := by
    refine ⟨ball a (r/16000),ball_mem_nhds a (by positivity),?_⟩
    intro d hd
    obtain ⟨z,⟨b,hb,rfl⟩,hdb⟩:=hd
    apply deck_ext hr hc g b
    change d • b=b
    apply (coverData hr hc g).nearby_unique
    · have hh:=dist_triangle (d • b) a b
      have hb' : dist b a < r/16000 := hb
      have hd' : dist (d • b) a < r/16000 := hdb
      rw [dist_comm a b] at hh
      linarith
    · exact deck_endpoint d b

omit hr hc g in
def deckIsometry (hr : 0 < r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X) (d : Deck o) :
    letI := intrinsicMetric (o:=o) hr hc g
    LocalGeodesic o ≃ᵢ LocalGeodesic o := by
  letI := intrinsicMetric (o:=o) hr hc g
  exact {
    toEquiv := d.val.toEquiv
    isometry_toFun := Isometry.of_dist_eq (intrinsicDist_homeomorph hr hc g d.val d.property)}

omit hr hc g in
def deckIsometricAction (hr : 0 < r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X) :
    letI := intrinsicMetric (o:=o) hr hc g
    Deck o →* (LocalGeodesic o ≃ᵢ LocalGeodesic o) := by
  letI := intrinsicMetric (o:=o) hr hc g
  exact {
    toFun := deckIsometry hr hc g
    map_one' := IsometryEquiv.ext (fun _ => rfl)
    map_mul' := fun _ _ => IsometryEquiv.ext (fun _ => rfl)}

omit hr hc g in
def deckPiOneEquiv (hr : 0 < r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X) :
    FundamentalGroup X o ≃* Deck o :=
  ((deck_quotientCovering hr hc g).fundamentalGroupEquiv ⟨constant o,rfl⟩).trans (MulEquiv.inv' (Deck o)).symm

end HyperbolicObstruction.LocalGeodesic
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_DevelopmentProper
attribute [-instance] _root_.OAI.HyperbolicObstruction.LocalGeodesic.instContinuousConstSMulSubtypeHomeomorphMemSubgroupDeck _root_.OAI.HyperbolicObstruction.LocalGeodesic.instMulActionSubtypeHomeomorphMemSubgroupDeck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction
variable {E X : Type*} [MetricSpace E] [MetricSpace X]

namespace LocalGeodesic
variable [CompactSpace X] {r : ℝ} (hr : 0 < r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
variable {o : X}

lemma developed_smallBall_compact (a : LocalGeodesic o) :
    @IsCompact (LocalGeodesic o) (intrinsicMetric hr hc g).toUniformSpace.toTopologicalSpace
      (@closedBall (LocalGeodesic o) (intrinsicMetric hr hc g).toPseudoMetricSpace a (r/32000)) := by
  have he : @closedBall (LocalGeodesic o) (intrinsicMetric hr hc g).toPseudoMetricSpace a (r/32000)=
      closedBall a (r/32000) := by
    ext b
    change intrinsicDist hr hc g b a ≤ r/32000 ↔ dist b a ≤ r/32000
    constructor
    · intro h; exact (ordinary_dist_le_intrinsic hr hc g b a).trans h
    · intro h
      rw [intrinsicDist_eq_of_close hr hc g (by linarith : dist b a < r/8000)]
      exact h
  rw [he]
  exact (coverData hr hc g).isCompact_closedBall a (by linarith : r/32000<(r/2000)/4)

lemma developed_proper : @ProperSpace (LocalGeodesic o) (intrinsicMetric hr hc g).toPseudoMetricSpace :=
  @proper_of_uniform_compact_balls (LocalGeodesic o) (intrinsicMetric hr hc g)
    (developed_isGeodesic hr hc g) (r/32000) (by positivity) (developed_smallBall_compact hr hc g)
end LocalGeodesic
end HyperbolicObstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_DevelopmentGeometricAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction.LocalGeodesic
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable {r : ℝ} (hr : 0 < r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)
variable {o : X}

lemma rebase_constant_apply (a : LocalGeodesic o) : rebase hr hc g (constant o) a=a := by
  apply congrFun ((isCoveringMap hr hc g).eq_of_comp_eq (rebase hr hc g (constant o)).continuous continuous_id
    (by funext z; exact rebase_endpoint hr hc g (constant o) z) (constant o) (rebase_start hr hc g (constant o)))

lemma intrinsicDist_constant (a : LocalGeodesic o) : intrinsicDist hr hc g (constant o) a=a.length := by
  have hh : (rebase hr hc g (constant o)).symm a=a := by
    apply (Homeomorph.symm_apply_eq _).mpr
    exact (rebase_constant_apply hr hc g a).symm
  unfold intrinsicDist
  exact congrArg (@length X _ o) hh

def deckGeometricAction : @GeometricAction (Deck o) (LocalGeodesic o) _ (intrinsicMetric hr hc g) := by
  have hdisc := (coverData (o:=o) hr hc g).discrete_fiber o
  letI := intrinsicMetric (o:=o) hr hc g
  letI := developed_proper (o:=o) hr hc g
  refine ⟨deckIsometricAction hr hc g,?_,?_⟩
  · intro C hC
    let a : LocalGeodesic o := constant o
    obtain ⟨R,hR⟩:=hC.isBounded.subset_closedBall a
    let F : Set (LocalGeodesic o) := endpoint ⁻¹' {o}
    have hFclosed : IsClosed F := isClosed_singleton.preimage endpoint_continuous
    have hFdisc : IsDiscrete F := isDiscrete_iff_discreteTopology.mpr hdisc
    have hfin : (closedBall a (2*R) ∩ F).Finite :=
      ((isCompact_closedBall a (2*R)).inter_right hFclosed).finite (hFdisc.mono inter_subset_right)
    have hmap : Function.Injective (fun d : Deck o => d • a) := fun d e h => deck_ext hr hc g a h
    apply ((hfin.preimage hmap.injOn)).subset
    intro d hd
    obtain ⟨x,hx,hdx⟩:=hd
    refine ⟨?_,?_⟩
    · have hx' : dist x a≤R := hR hx
      have hdx' : dist (d • x) a≤R := hR hdx
      have he : dist (d • a) (d • x)=dist a x := (deckIsometry hr hc g d).isometry.dist_eq a x
      have ht:=dist_triangle (d • a) (d • x) a
      rw [he,dist_comm a x] at ht
      exact ht.trans (by linarith)
    · change endpoint (d • a)=o
      rw [deck_endpoint]
      rfl
  · obtain ⟨R,hR⟩:=(isCompact_univ : IsCompact (univ : Set X)).isBounded.subset_closedBall o
    refine ⟨closedBall (constant o) R,isCompact_closedBall _ _,?_⟩
    intro b
    let c : LocalGeodesic o := ofReal (g.segment_spec o (endpoint b)).isLocalSegment (g.segment_spec o (endpoint b)).1
    have hcend : endpoint c=endpoint b := (g.segment_spec o (endpoint b)).2.1
    have hcC : c ∈ closedBall (constant o) R := by
      change intrinsicDist hr hc g c (constant o)≤R
      rw [intrinsicDist_comm,intrinsicDist_constant]
      change (ofReal (g.segment_spec o (endpoint b)).isLocalSegment (g.segment_spec o (endpoint b)).1).length≤R
      rw [ofReal_length]
      have hh : dist (endpoint b) o≤R := hR (mem_univ _)
      simpa [dist_comm] using hh
    obtain ⟨d,hd⟩:=deck_exists hr hc g c b hcend.symm
    exact ⟨d,c,hcC,hd⟩

end HyperbolicObstruction.LocalGeodesic
end
end

end OAI
end


