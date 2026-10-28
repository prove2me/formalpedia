-- Prove2me | Definitions.Def_OAIQ021F004
-- name    : OAIQ021F004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T18:10:29.017298+00:00
-- url     : https://prove2.me/theorems/d8179132-c6d5-429a-b495-dfd233069678
-- title:
--   Definitions bundle OAIQ021F004 of the split of OpenAI, Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.FKCRT.finite_fk_maps_converge_to_brownian_crt`, carved from OpenAI's openai/math development (OpenAI, *Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211)*, OpenAI Math Release, September 24, 2026, result family 211, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 113 declarations of OpenAI's Lean: 66 definitions, 10 instances and 37 theorems. The definitions and types are `OAI.FKCRT.Inventory.CoreTree.commonRoute`, `OAI.FKCRT.Inventory.CoreTree.dartCorners`, `OAI.FKCRT.Inventory.CoreTree.degrees`, `OAI.FKCRT.Inventory.CoreTree.depth`, `OAI.FKCRT.Inventory.CoreTree.labelEquiv`, `OAI.FKCRT.Inventory.CoreTree.markedWordEquiv`, `OAI.FKCRT.Inventory.CoreTree.maxDegree`, `OAI.FKCRT.Inventory.CoreTree.nodeEquiv`, `OAI.FKCRT.Inventory.CoreTree.nodePoint`, `OAI.FKCRT.Inventory.CoreTree.nodeSpine`, `OAI.FKCRT.Inventory.CoreTree.nonrootVertex`, `OAI.FKCRT.Inventory.CoreTree.ofMarkedCode`, `OAI.FKCRT.Inventory.CoreTree.productMass`, `OAI.FKCRT.Inventory.CoreTree.realDistance`, `OAI.FKCRT.Inventory.CoreTree.realizedPole`, `OAI.FKCRT.Inventory.CoreTree.root`, `OAI.FKCRT.Inventory.CoreTree.rootDart`, `OAI.FKCRT.Inventory.CoreTree.routeLength`, `OAI.FKCRT.Inventory.CoreTree.shape`, `OAI.FKCRT.Inventory.CoreTree.sizedEquiv`, `OAI.FKCRT.Inventory.CoreTree.sizedListEquiv`, `OAI.FKCRT.Inventory.CoreTree.sizedWordEquiv`, `OAI.FKCRT.Inventory.CoreTree.successfulMarkedEquiv`, `OAI.FKCRT.Inventory.CoreTree.timeVertex`, `OAI.FKCRT.Inventory.CoreTree.toCode`, `OAI.FKCRT.Inventory.CoreTree.toWord`, `OAI.FKCRT.Inventory.CoreTree.wordEquiv`, `OAI.FKCRT.Inventory.CoreTree.wordNodeEquiv`, `OAI.FKCRT.Inventory.actualDrawLaw`, `OAI.FKCRT.Inventory.actualHeight`, `OAI.FKCRT.Inventory.actualOffspring`, `OAI.FKCRT.Inventory.crtScale`, `OAI.FKCRT.Inventory.edgeScale`, `OAI.FKCRT.Inventory.metricBad`, `OAI.FKCRT.Inventory.metricMean`, `OAI.FKCRT.TreeCoding.CriticalEvenOffspring.PrefixDominatedFraction`, `OAI.FKCRT.TreeCoding.CriticalEvenOffspring.bridgeConstant`, `OAI.FKCRT.TreeCoding.CriticalEvenOffspring.bridgeFourier`, `OAI.FKCRT.TreeCoding.CriticalEvenOffspring.codeLaw`, `OAI.FKCRT.TreeCoding.CriticalEvenOffspring.iidBridgeLaw` and 26 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability/FKMaps, in whole or in part: `FKMaps_BlockLaw`, `FKMaps_BridgeLimit`, `FKMaps_ConditionedTrees`, `FKMaps_ConditionedWalk`, `FKMaps_CoreMetric`, `FKMaps_CornerMass`, `FKMaps_ExcursionLaw`, `FKMaps_FiniteLaw`, `FKMaps_GHPBounds`, `FKMaps_HeightBounds`, `FKMaps_HeightCoding`, `FKMaps_HeightTightness`, `FKMaps_MarkedSpines`, `FKMaps_MeasuredCoding`, `FKMaps_MetricLimit`, `FKMaps_NodeMetric`, `FKMaps_NodeOrder`, `FKMaps_Offspring`, `FKMaps_PieceLaws`, `FKMaps_PlaneTrees`, `FKMaps_SimpleWalk`, `FKMaps_SpineBounds`, `FKMaps_TreeCode`.
--
--   **Imports.** It imports the published bundle `Def_FKCRT`; the bundles `OAIQ021F002` and `OAIQ021F003` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.FKCRT.Inventory.actualHeight_CLT`, `OAI.FKCRT.Inventory.actual_map_tests`, `OAI.FKCRT.Inventory.metric_test_local`, `OAI.FKCRT.TreeCoding.CriticalEvenOffspring.jointCode_vervaat_CLT` and `OAI.FKCRT.TreeCoding.CriticalEvenOffspring.uniform_degree_spine_limit`; the proofs of `OAI.FKCRT.Inventory.actualHeight_CLT`, `OAI.FKCRT.Inventory.actual_map_tests`, `OAI.FKCRT.Inventory.metric_test_local`, `OAI.FKCRT.TreeCoding.CriticalEvenOffspring.jointCode_vervaat_CLT`, `OAI.FKCRT.TreeCoding.CriticalEvenOffspring.uniform_degree_spine_limit` and `OAI.FKCRT.finite_fk_maps_converge_to_brownian_crt`.
-- source:
--   OpenAI, Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 211; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Brownian-continuum-random-tree-limits-of-finite-Fortuin-Kasteleyn-maps-above-four-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/FKMaps at commit adc7f12

import Mathlib
import Definitions.Def_FKCRT
import Definitions.Def_OAIQ021F002
import Definitions.Def_OAIQ021F003

section
-- module Solutions.OAIQ021_FK.FKMaps_Offspring
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding


def CriticalEvenOffspring.streamStep (p : CriticalEvenOffspring) (j : ℕ) (ω : ℕ → ℕ) : ℝ :=
  p.standardStep (ω j)


def CriticalEvenOffspring.iidWalk (p : CriticalEvenOffspring) (N : ℕ)
    (d : Fin N → ℕ) : C(unitInterval, ℝ) :=
  interpolation N (fun i =>
    (∑ j : Fin N, if j.val < i.val then p.standardStep (d j) else 0) / Real.sqrt N)


def CriticalEvenOffspring.prefixWalk (p : CriticalEvenOffspring) (m r : ℕ)
    (t : unitInterval) (d : Fin m → ℕ) : C(unitInterval,ℝ) :=
  stopPath t (p.iidWalk (m+r) ((iidSplit m r).symm (d,fun _ => 1)))


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_BridgeLimit
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma CriticalEvenOffspring.iid_endpoint_positive (p : CriticalEvenOffspring) (n : ℕ) :
    0 < (p.iidLaw (2*n+1)).real {d | totalStep d = -1} := by
  have hlen : 2*n+1 = n+(n+1) := by omega
  rw [hlen]
  let d : Fin (n+(n+1)) → ℕ := (iidSplit n (n+1)).symm (fun _ => 2,fun _ => 0)
  have hd : iidSplit n (n+1) d = (fun _ => 2,fun _ => 0) :=
    (iidSplit n (n+1)).apply_symm_apply _
  have htotal : totalStep d = -1 := by
    rw [totalStep_split,hd]
    simp [totalStep]
  have hval (i : Fin (n+(n+1))) : d i=2 ∨ d i=0 := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact Or.inl (congrFun (congrArg Prod.fst hd) j)
    · exact Or.inr (congrFun (congrArg Prod.snd hd) j)
  have hsing : 0 < (p.iidLaw (n+(n+1))) {d} := by
    rw [iidLaw,Measure.pi_singleton]
    apply pos_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply ne_of_gt
    rw [p.law_singleton,ENNReal.ofReal_pos]
    rcases hval i with h|h
    · simpa only [h] using p.two_pos
    · simpa only [h] using p.zero_pos
  have hpos : 0 < (p.iidLaw (n+(n+1))) {d | totalStep d = -1} := by
    apply hsing.trans_le
    exact measure_mono (Set.singleton_subset_iff.mpr htotal)
  exact ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)

def CriticalEvenOffspring.iidBridgeLaw (p : CriticalEvenOffspring) (n : ℕ) :
    Measure (Fin (2*n+1) → ℕ) := cond (p.iidLaw (2*n+1)) {d | totalStep d = -1}

instance instIsProbabilityMeasureForallFinHAddNatHMulOfNatIidBridgeLaw (p : CriticalEvenOffspring) (n : ℕ) : IsProbabilityMeasure (p.iidBridgeLaw n) := by
  apply cond_isProbabilityMeasure
  exact fun h => (p.iid_endpoint_positive n).ne' (by simp [measureReal_def,h])

def CriticalEvenOffspring.bridgeConstant (p : CriticalEvenOffspring) : ℝ :=
  Real.sqrt (2*Real.pi)/(p.sigma*Real.pi)

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_TreeCode
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.codeMarkLaw_probability _root_.OAI.FKCRT.TreeCoding.instMeasurableSingletonClassCode _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding


def codePartition (p : CriticalEvenOffspring) (N : ℕ) : ℝ :=
  ∑ d : Code N, codeWeight p d


lemma codePartition_odd_pos (p : CriticalEvenOffspring) (n : ℕ) :
    0 < codePartition p (2*n+1) := by
  apply lt_of_lt_of_le (codeWeight_binaryComb_pos p n)
  exact Finset.single_le_sum (fun d _ => codeWeight_nonneg p d) (Finset.mem_univ _)


instance instFintypeBridge (N : ℕ) : Fintype (Bridge N) := Fintype.ofFinite _


def rotateBridge {N : ℕ} [NeZero N] (m : Fin N) : Equiv.Perm (Bridge N) :=
  (rotateDegrees m).subtypeEquiv (fun d => by rw [walk_rotate_terminal])


lemma Bridge.unique_good_rotation {N : ℕ} [NeZero N] (d : Bridge N) :
    ∃! m : Fin N, IsTreeCode (rotateBridge m d).val := by
  have hs : (degreeList d.val).sum = -1 := (degreeList_sum _).trans d.property
  obtain ⟨m, hm, huniq⟩ := existsUnique_excursion_rotation hs
  refine ⟨⟨m, by simpa using hm.1⟩, ?_, ?_⟩
  · change IsTreeCode (rotateDegrees ⟨m, by simpa using hm.1⟩ d.val)
    rw [isTreeCode_iff]
    exact (degreeList_rotate ⟨m, by simpa using hm.1⟩ d.val).symm ▸ hm.2
  · intro k hk
    apply Fin.ext
    apply huniq _
    refine ⟨by simpa only [degreeList_length] using k.isLt, ?_⟩
    rw [isTreeCode_iff] at hk
    simpa only [rotateBridge, Equiv.subtypeEquiv_apply, degreeList_rotate] using hk


def bridgeWeight {N : ℕ} (p : CriticalEvenOffspring) (d : Bridge N) : ℝ :=
  ∏ i : Fin N, p.mass (d.val i).val


def bridgePartition (p : CriticalEvenOffspring) (N : ℕ) : ℝ :=
  ∑ d : Bridge N, bridgeWeight p d


lemma bridgeWeight_rotate {N : ℕ} [NeZero N] (p : CriticalEvenOffspring)
    (d : Bridge N) (m : Fin N) : bridgeWeight p (rotateBridge m d) = bridgeWeight p d := by
  exact Equiv.prod_comp (Equiv.addRight m) (fun i => p.mass (d.val i).val)


theorem codePartition_cyclic (p : CriticalEvenOffspring) {N : ℕ} (hN : 0 < N) :
    bridgePartition p N = (N : ℝ) * codePartition p N := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  have h := weighted_unique_rotation (rotateBridge (N := N)) (bridgeWeight p)
    (fun d => IsTreeCode d.val) (fun m d => bridgeWeight_rotate p d m)
    (fun d => d.unique_good_rotation)
  rw [Fintype.card_fin] at h
  change (∑ d : Bridge N, bridgeWeight p d) = _
  rw [h]
  congr 1
  rw [← Finset.sum_filter]
  unfold codePartition
  rw [Finset.sum_subtype (p := fun d : Bridge N => IsTreeCode d.val) _ (by simp)]
  let e : Code N ≃ {d : Bridge N // IsTreeCode d.val} := {
    toFun := fun d => ⟨⟨d.val, d.property.1⟩, d.property⟩
    invFun := fun d => ⟨d.val.val, d.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact (Equiv.sum_comp e (fun d => bridgeWeight p d.val)).symm


def bridgeEmbedding (N : ℕ) : Bridge N ↪ (Fin N → ℕ) where
  toFun d i := (d.val i).val
  inj' := by
    intro d e h
    apply Subtype.ext
    funext i
    exact Fin.ext (congrFun h i)


lemma totalStep_bridge {N : ℕ} (d : Bridge N) : totalStep (bridgeEmbedding N d) = -1 := by
  have heq : totalStep (bridgeEmbedding N d) = walk d.val N := by
    simp only [totalStep, walk, Fin.is_lt, ite_true]
    rfl
  exact heq.trans d.property


lemma totalStep_bridge_range (N : ℕ) :
    {d : Fin N → ℕ | totalStep d = -1} = Set.range (bridgeEmbedding N) := by
  ext d
  constructor
  · intro hd
    have hsum : (∑ i, d i) + 1 = N := by
      rw [Set.mem_ofPred_eq, totalStep_eq_sum_sub] at hd
      omega
    have hbound (i : Fin N) : d i < N := by
      have hle : d i ≤ ∑ k, d k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    let f : Fin N → Fin N := fun i => ⟨d i, hbound i⟩
    have hf : walk f N = -1 := by
      have : walk f N = totalStep d := by simp [walk, totalStep, f]
      exact this.trans hd
    exact ⟨⟨f, hf⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact totalStep_bridge b


lemma CriticalEvenOffspring.bridgePartition_eq_iid (p : CriticalEvenOffspring) (N : ℕ) :
    bridgePartition p N = (p.iidLaw N).real {d | totalStep d = -1} := by
  classical
  have hset : {d : Fin N → ℕ | totalStep d = -1} =
      ⋃ b : Bridge N, {bridgeEmbedding N b} := by
    rw [totalStep_bridge_range]
    ext d
    simp
  have hdis : Pairwise (fun b c : Bridge N => Disjoint ({bridgeEmbedding N b} : Set (Fin N → ℕ)) {bridgeEmbedding N c}) := by
    intro b c hbc
    exact Set.disjoint_singleton.mpr ((bridgeEmbedding N).injective.ne hbc)
  rw [measureReal_def, hset, measure_iUnion hdis (fun _ => measurableSet_singleton _),
    tsum_fintype, ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
  apply Finset.sum_congr rfl
  intro b _
  rw [CriticalEvenOffspring.iidLaw, Measure.pi_singleton, ENNReal.toReal_prod]
  simp only [p.law_singleton, ENNReal.toReal_ofReal (p.nonneg _)]
  rfl


@[simp] lemma rotateBridge_zero {N : ℕ} [NeZero N] (d : Bridge N) :
    rotateBridge (0 : Fin N) d = d := by
  apply Subtype.ext
  funext i
  simp [rotateBridge, rotateDegrees]


def goodRotation {N : ℕ} [NeZero N] (d : Bridge N) : Fin N :=
  d.unique_good_rotation.exists.choose


lemma goodRotation_spec {N : ℕ} [NeZero N] (d : Bridge N) :
    IsTreeCode (rotateBridge (goodRotation d) d).val :=
  d.unique_good_rotation.exists.choose_spec


def canonicalCode {N : ℕ} [NeZero N] (d : Bridge N) : Code N :=
  ⟨(rotateBridge (goodRotation d) d).val, goodRotation_spec d⟩


def bridgeFromArray {N : ℕ} (d : Fin N → ℕ) (hd : totalStep d = -1) : Bridge N :=
  ((totalStep_bridge_range N) ▸ hd : d ∈ Set.range (bridgeEmbedding N)).choose


def arrayTree (n : ℕ) (d : Fin (2*n+1) → ℕ) : Code (2*n+1) := by
  let : NeZero (2*n+1) := ⟨by omega⟩
  exact if h : totalStep d = -1 then canonicalCode (bridgeFromArray d h) else binaryComb n


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_HeightCoding
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.codeMarkLaw_probability _root_.OAI.FKCRT.TreeCoding.instMeasurableSingletonClassCode _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding


def CriticalEvenOffspring.bridgeFourier (p : CriticalEvenOffspring) (n : ℕ) (t : ℝ) : ℂ :=
  p.fourierCutoff n t * Complex.exp ((t / (p.sigma * Real.sqrt (n+1)) : ℝ) * Complex.I)


noncomputable def codeEventMass (p : CriticalEvenOffspring) (N : ℕ)
    (E : (Fin N → Fin N) → Prop) : ℝ := by
  classical
  exact ∑ d : Code N, if E d.val then codeWeight p d else 0


noncomputable def bridgeEventMass (p : CriticalEvenOffspring) (N : ℕ)
    (E : (Fin N → Fin N) → Prop) : ℝ := by
  classical
  exact ∑ d : Bridge N, if E d.val then bridgeWeight p d else 0


def codeEventProbability (p : CriticalEvenOffspring) (N : ℕ)
    (E : (Fin N → Fin N) → Prop) : ℝ :=
  codeEventMass p N E / codePartition p N


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_ConditionedWalk
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding


def CriticalEvenOffspring.iidSiteProbability (p : CriticalEvenOffspring) (N : ℕ)
    (j : ℤ) : ℝ := (p.iidLaw N).real {d | totalStep d = j}


end FKCRT.TreeCoding

namespace FKCRT.TreeCoding


def CriticalEvenOffspring.PrefixDominatedFraction (p : CriticalEvenOffspring)
    (N J : ℕ) (K : ℝ) : Prop :=
  ∀ m r : ℕ, m+r=N → N ≤ J*r → ∀ E : Set (Fin m → ℕ),
    (cond (p.iidLaw (m+r)) {d | totalStep d = -1}).real
      {d | (iidSplit m r d).1 ∈ E} ≤ K * (p.iidLaw m).real E


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_HeightBounds
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.codeMarkLaw_probability _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

def CriticalEvenOffspring.codeLaw (p : CriticalEvenOffspring) (n : ℕ) : Measure (Code (2*n+1)) :=
  (p.iidBridgeLaw n).map (arrayTree n)

instance instIsProbabilityMeasureCodeHAddNatHMulOfNatCodeLaw (p : CriticalEvenOffspring) (n : ℕ) : IsProbabilityMeasure (p.codeLaw n) :=
  Measure.isProbabilityMeasure_map (measurable_of_countable (arrayTree n)).aemeasurable

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_HeightTightness
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.codeMarkLaw_probability _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

def codeEmbedding (N : ℕ) : Code N ↪ (Fin N → ℕ) :=
  ⟨fun d => bridgeEmbedding N ⟨d.val,d.property.1⟩, fun _ _ h =>
    Subtype.ext (congrArg (fun b : Bridge N => b.val) ((bridgeEmbedding N).injective h))⟩

end FKCRT.TreeCoding
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_SimpleWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

lemma killed_symm (n a b : ℕ) : killed n a b=killed n b a := by
  rw [killed_reflection,killed_reflection,show (a:ℤ)-b=-((b:ℤ)-a) by ring,kernel_symm]
  congr 2; ring

lemma kernel_adjacent (n b : ℕ) :
    ((n:ℝ)+b+2)*kernel n ((b:ℤ)+2)=((n:ℝ)-b)*kernel n b := by
  rw [kernel_binomial,kernel_binomial]
  by_cases he : ((b:ℤ)+n)%2=0
  · have he' : ((b:ℤ)+2+n)%2=0 := by omega
    have hd : ((b:ℤ)+2+n)/2=((b:ℤ)+n)/2+1 := by omega
    rw [ite_eq_left he,ite_eq_left he',hd]
    have hk : 0≤((b:ℤ)+n)/2 := by omega
    have hc := chooseInt_adjacent n (((b:ℤ)+n)/2) hk
    have hr : 2*(((b:ℤ)+n)/2:ℤ)=(b:ℤ)+n := by omega
    have hr' : 2*((((b:ℤ)+n)/2:ℤ):ℝ)=(b:ℝ)+n := by exact_mod_cast hr
    have h1 : (n:ℝ)+b+2=2*((((b:ℤ)+n)/2:ℤ):ℝ)+2 := by linarith
    have h2 : (n:ℝ)-b=2*((n:ℝ)-((((b:ℤ)+n)/2:ℤ):ℝ)) := by linarith
    rw [h1,h2]
    rw [← mul_div_assoc,← mul_div_assoc]
    congr 1
    nlinarith
  · have he' : ((b:ℤ)+2+n)%2≠0 := by omega
    simp only [he,he',ite_false,mul_zero]

/-- Exact entrance density, including the zero-time and unreachable cases. -/
theorem killed_entrance (n b : ℕ) :
    killed n 0 b = (2*((b:ℝ)+1)/((n:ℝ)+b+2))*kernel n b := by
  rw [killed_reflection]
  simp only [Nat.cast_zero,sub_zero,add_zero]
  have he := kernel_adjacent n b
  have hp : (0:ℝ)<n+b+2 := by positivity
  field_simp
  nlinarith

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

lemma binary_partition (n : ℕ) :
    codePartition binaryOffspring (2*n+1)=SimpleWalk.kernel (2*n+1) (-1)/(2*n+1:ℕ) := by
  have h := codePartition_cyclic binaryOffspring (by omega : 0<2*n+1)
  rw [binaryOffspring.bridgePartition_eq_iid,binary_kernel] at h
  apply (eq_div_iff (by positivity : ((2*n+1:ℕ):ℝ)≠0)).mpr
  linarith

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
attribute [local instance] Classical.propDecidable

/-- Ballot/first-hitting formula, without parity or reachability restrictions. -/
theorem firstHit_formula (n a : ℕ) :
    pathMass (n+1) (firstHit a)=((a:ℝ)+1)/((n:ℝ)+1)*kernel (n+1) ((a:ℤ)+1) := by
  rw [pathMass_firstHit,killed_symm,killed_entrance,kernel_succ]
  rw [show (a:ℤ)+1-1=a by ring,show (a:ℤ)+1+1=a+2 by ring]
  have h := kernel_adjacent n a
  have hn : (n:ℝ)+1≠0 := by positivity
  have ha : (n:ℝ)+a+2≠0 := by positivity
  field_simp
  nlinarith

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
open TreeCoding
attribute [local instance] Classical.propDecidable

lemma firstHit_mass_pos (n : ℕ) : 0<pathMass (2*n+1) (firstHit 0) := by
  rw [firstHit_formula]
  norm_num only [Nat.cast_zero,Int.natCast_zero,zero_add,one_mul]
  rw [← kernel_symm (2*n+1) 1]
  have h := codePartition_odd_pos binaryOffspring n
  rw [binary_partition] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  ring

instance excursionLaw_probability (n : ℕ) : IsProbabilityMeasure (excursionLaw n) := by
  apply cond_isProbabilityMeasure
  intro h
  have hp := firstHit_mass_pos n
  change 0<pathMass (2*n+1) (fun d => d∈{d | firstHit 0 d}) at hp
  rw [← uniformLaw_real] at hp
  simp only [measureReal_def,h,ENNReal.toReal_zero,lt_self_iff_false] at hp

end FKCRT.SimpleWalk
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_PlaneTrees
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation _root_.OAI.FKCRT.Inventory.CoreLabel.instMeasurableSingletonClass _root_.OAI.FKCRT.Inventory.CoreLabel.instMeasurableSpace _root_.OAI.FKCRT.Inventory.CoreTree.instDecidableEqDart _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory

namespace CoreTree

lemma word_injective : Function.Injective word := by
  intro t
  induction t with
  | leaf =>
    intro u h
    cases u with
    | leaf => rfl
    | branch c us => exact False.elim (branch_nonempty c us h.symm)
  | branch c ts ih =>
    intro u h
    cases u with
    | leaf => exact False.elim (branch_nonempty c ts h)
    | branch d us =>
      have hvc (c : Core) (ts : Fin c.val.length→ CoreTree) :
          ValidCorners (cornerList c (fun i => (ts i).word)) := by
        exact cornerList_valid c (fun i => ⟨(ts i).word,(ts i).word_empty⟩)
      have hh := valid_corner_injective (hvc c ts) (hvc d us) h
      have hcd := cornerList_congr_core hh
      subst d
      have hwords := cornerList_injective c hh
      have hts : ts=us := by
        funext i
        exact ih i (congrFun hwords i)
      rw [hts]

end CoreTree

/-- The finite recursive forest construction terminates because actual
corner words are strictly shorter. -/
theorem exists_core_tree (w : List TypedLetter) (hw : stackTypedRun w []=some []) :
    ∃ t : CoreTree,t.word=w := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases he : w=[]
    · exact ⟨.leaf,he.symm⟩
    let W : NonemptyTypedWord := ⟨⟨w,hw⟩,he⟩
    let d := coreChildrenEquiv.symm W
    have hd : cornerInsert (cornerList d.1 (fun i => (d.2 i).val))=w :=
      congrArg (fun w => w.val.val) (coreChildrenEquiv.apply_symm_apply W)
    have hshort (i : Fin d.1.val.length) : (d.2 i).val.length<n := by
      have hh := corner_child_short (cornerList d.1 (fun i => (d.2 i).val))
        (d.1.val.get i,(d.2 i).val) (List.mem_ofFn.mpr ⟨i,rfl⟩)
      rwa [hd,hn] at hh
    have hchild (i : Fin d.1.val.length) : ∃ t : CoreTree,t.word=(d.2 i).val :=
      ih _ (hshort i) _ (d.2 i).property rfl
    let ts := fun i => (hchild i).choose
    refine ⟨.branch d.1 ts,?_⟩
    change cornerInsert (cornerList d.1 (fun i => (ts i).word))=w
    have ht : (fun i => (ts i).word)=(fun i => (d.2 i).val) :=
      funext (fun i => (hchild i).choose_spec)
    rw [ht,hd]

namespace CoreTree

def toWord (t : CoreTree) : EmptyTypedWord := ⟨t.word,t.word_empty⟩

lemma toWord_bijective : Function.Bijective toWord := by
  constructor
  · intro t u h
    exact word_injective (congrArg Subtype.val h)
  · intro w
    obtain ⟨t,ht⟩ := exists_core_tree w.val w.property
    exact ⟨t,Subtype.ext ht⟩

/-- Full actual-word / normalized connected-core ordered-tree bijection. -/
def wordEquiv : CoreTree ≃ EmptyTypedWord := Equiv.ofBijective toWord toWord_bijective

end CoreTree
end FKCRT.Inventory
end


noncomputable section
open List
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

namespace CoreTree

def degrees (t : CoreTree) : List ℕ := t.labels.map CoreLabel.arity

lemma labels_injective : Function.Injective labels := by
  intro T U h
  have hh := congrArg (fun l => build l []) h
  simpa only [build_labels,List.cons.injEq,and_true] using hh

/-- The actual labelled arity excursion determines exactly one connected-core
ordered tree. No probabilistic independence is part of this statement. -/
theorem exists_of_excursion {l : List CoreLabel}
    (h : FKCRT.TreeCoding.IsExcursionList
      (FKCRT.TreeCoding.PlaneTree.incrementWord (l.map CoreLabel.arity))) :
    ∃ T : CoreTree,T.labels=l := by
  obtain ⟨he,hlen⟩ := build_correct (FKCRT.TreeCoding.PlaneTree.suffixNegative_of_excursion h)
  rw [h.1] at hlen
  have hl : (build l []).length=1 := by omega
  obtain ⟨T,hT⟩ := List.length_eq_one_iff.mp hl
  exact ⟨T,by simpa [hT] using he⟩

end CoreTree
end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_PieceLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

instance instMeasurableSingletonClassOrder : MeasurableSingletonClass Order := ⟨fun _ => trivial⟩

end FKCRT.Inventory
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_ExcursionLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
open TreeCoding

lemma histogram_probability {m : ℕ} (u : Fin (m+1) → unitInterval) (n : ℕ) :
    IsProbabilityMeasure (volume.withDensity (histogramDensity u n)) := by
  rw [show histogramDensity u n=Histogram.density (excursionLaw n) (gridSample u n) (mesh n) from rfl,
    ← Histogram.mixture_withDensity]
  exact Histogram.mixture_probability _ _ (mesh_pos n)

end FKCRT.SimpleWalk
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_BlockLaw
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation _root_.OAI.FKCRT.Inventory.CoreLabel.instMeasurableSingletonClass _root_.OAI.FKCRT.Inventory.CoreLabel.instMeasurableSpace _root_.OAI.FKCRT.Inventory.CoreTree.instDecidableEqDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open List Filter
open scoped BigOperators Topology
namespace FKCRT.Inventory
open MapCycles Chords
attribute [local instance] Classical.propDecidable

/-- The actual corner offspring distribution, not an abstract replacement. -/
def actualOffspring (P : Parameters) : FKCRT.TreeCoding.CriticalEvenOffspring :=
  FKCRT.BlockCritical.evenOffspring
    ⟨actualBlockMass P,actualBlockMass_nonneg P,(actual_block_moments P).1⟩
    (actualBlockMass_zero_pos P) (actualBlockMass_one_pos P)
    (actual_block_moments P).2.1 (actual_block_moments P).2.2

end FKCRT.Inventory
end


noncomputable section
open List Equiv MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

namespace CoreTree
/-- Product of genuine root-core probabilities at every vertex. -/
def productMass (t r τ : ℝ) : CoreTree→ℝ
  | leaf => 1/τ
  | branch c ts => (wordMonomial t (r*τ) c.val/τ)*∏ i,productMass t r τ (ts i)

end CoreTree

end FKCRT.Inventory
end


noncomputable section
open List
open scoped BigOperators
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

namespace CoreTree

def shape : CoreTree → FKCRT.TreeCoding.PlaneTree
  | leaf => .node []
  | branch _c ts => .node (List.ofFn (fun i => shape (ts i)))

lemma shape_degrees (T : CoreTree) : T.shape.degrees=T.degrees := by
  induction T with
  | leaf => simp [shape,FKCRT.TreeCoding.PlaneTree.degrees,degrees,labels,CoreLabel.arity]
  | branch c ts ih =>
    rw [shape,FKCRT.TreeCoding.PlaneTree.degrees,degrees,labels_branch]
    simp only [List.length_ofFn,List.map_cons,CoreLabel.arity,List.flatMap_def,
      List.map_flatten,List.map_ofFn,Function.comp_def]
    congr 2
    exact congrArg List.ofFn (funext ih)

lemma degrees_excursion (T : CoreTree) : FKCRT.TreeCoding.IsExcursionList
    (FKCRT.TreeCoding.PlaneTree.incrementWord T.degrees) := by
  rw [← shape_degrees]
  exact T.shape.degrees_excursion

def labelEquiv : CoreTree ≃ LabelExcursion :=
  Equiv.ofBijective (fun T => ⟨T.labels,T.degrees_excursion⟩) ⟨by
    intro T U h
    exact labels_injective (congrArg Subtype.val h),by
    intro l
    obtain ⟨T,hT⟩ := exists_of_excursion l.property
    exact ⟨T,Subtype.ext hT⟩⟩

end CoreTree
end FKCRT.Inventory
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_SpineBounds
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.codeMarkLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

/-- The exact deterministic ancestral statistic at preorder position v. -/
def codeSpineSum {N : ℕ} (b : ℕ×ℕ → ℝ) (d : Code N) (v : ℕ) : ℝ :=
  recordSpineSum b (reverseFirst v (arrayStream (codeEmbedding N d))) v

end FKCRT.TreeCoding
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_MarkedSpines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

abbrev SpineRecords {N : ℕ} (d : Code N) (v : ℕ) :=
  ↥(weakRecords (integerSum (reverseFirst v (arrayStream (codeEmbedding N d)))) v)

def spineRecordType {N : ℕ} (d : Code N) (v : ℕ) (t : SpineRecords d v) : ℕ×ℕ :=
  recordTypeAt (reverseFirst v (arrayStream (codeEmbedding N d))) t.val

lemma spineRecord_bounds {N : ℕ} (d : Code N) (v : ℕ) (t : SpineRecords d v) :
    1 ≤ t.val ∧ t.val ≤ v := by
  have h := (mem_weakRecords _ _ _).mp t.property
  exact ⟨h.1,h.2.1⟩

def spineRecordVertex {N : ℕ} (d : Code N) {v : ℕ} (hv : v ≤ N) (t : SpineRecords d v) : Fin N :=
  ⟨v-t.val,by have h := spineRecord_bounds d v t; omega⟩

variable {A : Type*} [MeasurableSpace A]

def markedSpineSum {N : ℕ} (b : (ℕ×ℕ) → A → ℝ) (d : Code N) {v : ℕ}
    (hv : v ≤ N) (a : Fin N → A) : ℝ :=
  ∑ t : SpineRecords d v,b (spineRecordType d v t) (a (spineRecordVertex d hv t))

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

variable {A : Type*} [MeasurableSpace A]

def codeMarkKernel (κ : ℕ → Measure A) (N : ℕ) : Kernel (Code N) (Fin N → A) :=
  ⟨codeMarkLaw κ,measurable_of_countable _⟩

instance codeMarkKernel_markov (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)] (N : ℕ) :
    IsMarkovKernel (codeMarkKernel κ N) := ⟨fun _ => codeMarkLaw_probability _ _⟩

def CriticalEvenOffspring.markedCodeLaw (p : CriticalEvenOffspring) (κ : ℕ → Measure A) (n : ℕ) :
    Measure (Code (2*n+1) × (Fin (2*n+1) → A)) := p.codeLaw n ⊗ₘ codeMarkKernel κ (2*n+1)

instance CriticalEvenOffspring.markedCodeLaw_probability (p : CriticalEvenOffspring)
    (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)] (n : ℕ) :
    IsProbabilityMeasure (p.markedCodeLaw κ n) := by unfold CriticalEvenOffspring.markedCodeLaw; infer_instance

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_ConditionedTrees
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation _root_.OAI.FKCRT.Inventory.CoreTree.instDecidableEqDart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT.Inventory
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

namespace CoreTree

lemma word_length_degrees (T : CoreTree) : T.word.length=T.degrees.sum := by
  induction T with
  | leaf => simp [word,degrees,labels,CoreLabel.arity]
  | branch c ts ih =>
    have hw : (branch c ts).word.length=∑ i,(1+(ts i).word.length) := by
      simp [word,cornerInsert,cornerList,List.length_flatMap,List.map_ofFn,List.sum_ofFn,
        add_comm]
    have hd : (branch c ts).degrees.sum=c.val.length+∑ i,(ts i).degrees.sum := by
      simp [degrees,labels_branch,CoreLabel.arity,List.flatMap_def,List.map_flatten,
        List.sum_flatten,List.map_ofFn,List.sum_ofFn]
    rw [hw,hd]
    simp_rw [ih]
    simp [Finset.sum_add_distrib]

lemma labels_length (T : CoreTree) : T.labels.length=T.word.length+1 := by
  have h := T.shape.degrees_sum
  rw [T.shape_degrees,← T.word_length_degrees] at h
  simpa only [degrees,List.length_map] using h.symm

def toCode (T : CoreTree) : Code T.labels.length :=
  ⟨fun i => ⟨(T.labels[i.val]).arity,by
    have hm : (T.labels[i.val]).arity∈T.shape.degrees := by
      rw [T.shape_degrees]
      exact List.mem_map.mpr ⟨_,List.getElem_mem _,rfl⟩
    have hl := T.shape.degree_lt_length hm
    simpa only [shape_degrees,degrees,List.length_map] using hl⟩,by
    rw [isTreeCode_iff]
    convert T.degrees_excursion using 1
    all_goals try with_reducible_and_instances rfl
    unfold degreeList PlaneTree.incrementWord degrees
    simp only [List.map_map,Function.comp_def]
    exact List.ofFn_getElem_eq_map T.labels (fun c => (c.arity:ℤ)-1)⟩

def ofMarkedCode {N : ℕ} (x : MarkedCode N) : CoreTree :=
  labelEquiv.symm ⟨List.ofFn x.val.2,by
    have h : (List.ofFn x.val.2).map CoreLabel.arity=List.ofFn (fun i => (x.val.1.val i).val) := by
      simp only [List.map_ofFn,Function.comp_def]
      exact congrArg List.ofFn (funext x.property)
    rw [h,PlaneTree.incrementWord_ofFn]
    exact (isTreeCode_iff _).mp x.val.1.property⟩

lemma ofMarkedCode_labels {N : ℕ} (x : MarkedCode N) :
    (ofMarkedCode x).labels=List.ofFn x.val.2 :=
  congrArg Subtype.val (labelEquiv.apply_symm_apply _)

lemma ofMarkedCode_size {N : ℕ} (x : MarkedCode N) : (ofMarkedCode x).labels.length=N := by
  rw [ofMarkedCode_labels,List.length_ofFn]

lemma ofMarkedCode_injective (N : ℕ) : Function.Injective (@ofMarkedCode N) := by
  intro x y h
  have hl := congrArg labels h
  rw [ofMarkedCode_labels,ofMarkedCode_labels] at hl
  have ha : x.val.2=y.val.2 := List.ofFn_injective hl
  have hd : x.val.1=y.val.1 := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    rw [← x.property i,← y.property i,ha]
  exact Subtype.ext (Prod.ext hd ha)

def sizedEquiv (N : ℕ) : MarkedCode N ≃ Sized N := Equiv.ofBijective
  (fun x => ⟨ofMarkedCode x,ofMarkedCode_size x⟩) ⟨by
    intro x y h
    exact ofMarkedCode_injective N (congrArg Subtype.val h),by
    rintro ⟨T,hT⟩
    subst N
    let d : Code T.labels.length := T.toCode
    let a : Fin T.labels.length → CoreLabel := fun i => T.labels[i.val]
    have ha : List.ofFn a=T.labels := List.ofFn_getElem
    have hcomp : ∀ i,(a i).arity=(d.val i).val := fun _ => rfl
    refine ⟨⟨(d,a),hcomp⟩,Subtype.ext ?_⟩
    apply labels_injective
    rw [ofMarkedCode_labels,ha]⟩

end CoreTree

end FKCRT.Inventory
end


noncomputable section
open List Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT.Inventory
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

namespace CoreTree

/-- The actual successful words and compatible independently marked tree
codes are equivalent at each fixed total edge size. -/
def sizedWordEquiv (N : ℕ) : Sized (N+1) ≃ {w : EmptyTypedWord // w.val.length=N} :=
  Equiv.ofBijective (fun T => ⟨wordEquiv T.val,by
    have h := T.val.labels_length
    have hT := T.property
    change T.val.word.length=N
    omega⟩) ⟨by
      intro T U h
      exact Subtype.ext (word_injective (congrArg (fun w => w.val.val) h)),by
      rintro ⟨w,hw⟩
      let T := wordEquiv.symm w
      have hT : T.word=w.val := congrArg Subtype.val (wordEquiv.apply_symm_apply w)
      refine ⟨⟨T,?_⟩,Subtype.ext (Subtype.ext hT)⟩
      rw [T.labels_length,hT,hw]⟩

def markedWordEquiv (N : ℕ) : MarkedCode (N+1) ≃ SizedWord N :=
  (sizedEquiv (N+1)).trans (sizedWordEquiv N)

end CoreTree

end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_CoreMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Equiv Equiv.Perm MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace FKCRT.Inventory
open MapCycles PermutationWedge TreeCoding
attribute [local instance] Classical.propDecidable

/-- The source block-distance mean; finiteness uses only offspring variance. -/
def metricMean (P : Parameters) : ℝ :=
  ∫ z,∫ a,coreIncrement z a ∂(CoreLabel.markLaw P z.1).toMeasure ∂(actualOffspring P).spineLaw

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

instance instFintypeDart (t : CoreTree) : Fintype t.Dart := by
  induction t with
  | leaf => exact inferInstanceAs (Fintype Empty)
  | branch c ts ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Fin c.val.length ⊕ (Σ i, (ts i).Dart)))

def dartCorners (c : Core) (ts : Fin c.val.length→ CoreTree) :
    List ((branch c ts).Dart × List (branch c ts).Dart) :=
  (List.finRange _).map fun i => (coreDart ts i,(ts i).darts.map (childDart ts i))

end FKCRT.Inventory.CoreTree
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_NodeMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

instance instFintypeNode (t : CoreTree) : Fintype t.Node := by
  induction t with
  | leaf => exact inferInstanceAs (Fintype PUnit)
  | branch c ts ih =>
    letI := ih
    exact inferInstanceAs (Fintype (PUnit ⊕ (Σ i, (ts i).Node)))

instance instDecidableEqNode (t : CoreTree) : DecidableEq t.Node := Classical.decEq _

def root : (t : CoreTree) → t.Node
  | .leaf => PUnit.unit
  | .branch _ _ => .inl PUnit.unit

def rootDart : (t : CoreTree) → Option t.Dart
  | .leaf => none
  | .branch c ts => some (coreDart ts c.entry)

def routeLength : (t : CoreTree) → t.Node → ℕ
  | .leaf,_ => 0
  | .branch _ _,.inl _ => 0
  | .branch c ts,.inr ⟨i,v⟩ => c.increment i+routeLength (ts i) v

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

/-- Real graph distance, on the same literal original map. -/
def realDistance (t : CoreTree) (a b : t.Dart) : ℝ :=
  let s := t.darts.formPerm*turns t.matching.first
  (dartGraph t.matching.mate s).dist (vertex s a) (vertex s b)

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

namespace CoreTree

def commonRoute : (t : CoreTree) → t.Node → t.Node → ℕ
  | .leaf,_,_ => 0
  | .branch _ _,.inl _,_ => 0
  | .branch _ _,.inr _,.inl _ => 0
  | .branch c ts,.inr ⟨i,v⟩,.inr ⟨j,w⟩ =>
    if h : i=j then c.increment i+commonRoute (ts i) v (h.symm ▸ w) else 0

def maxDegree : CoreTree → ℕ
  | .leaf => 0
  | .branch c ts => max c.val.length (Finset.univ.sup (fun i => maxDegree (ts i)))

end CoreTree
end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_NodeOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open List Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace FKCRT.Inventory.CoreTree
open TreeCoding
attribute [local instance] Classical.propDecidable

lemma nodeIndex_bound (t : CoreTree) (v : t.Node) : t.nodeIndex v<t.labels.length := by
  induction t with
  | leaf => simp [nodeIndex,labels]
  | branch c ts ih =>
    cases v with
    | inl u => exact List.length_pos_iff.mpr (labels_nonempty _)
    | inr v =>
      obtain ⟨i,v⟩ := v
      rw [labels_split c ts i]
      simp only [nodeIndex,List.length_cons,List.length_append]
      have := ih i v
      omega

def nodeSpine (b : (ℕ×ℕ) → CoreLabel → ℝ) : (t : CoreTree) → t.Node → ℝ
  | .leaf,_ => 0
  | .branch _ _,.inl _ => 0
  | .branch c ts,.inr ⟨i,v⟩ => b (c.val.length,c.val.length-1-i.val) (some c)+nodeSpine b (ts i) v

def depth : (t : CoreTree) → t.Node → ℕ
  | .leaf,_ => 0
  | .branch _ _,.inl _ => 0
  | .branch _ ts,.inr ⟨i,v⟩ => 1+depth (ts i) v

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List
open scoped BigOperators
namespace FKCRT.Inventory.CoreTree
attribute [local instance] Classical.propDecidable

lemma offset_separation (c : Core) (ts : Fin c.val.length → CoreTree) (i j : Fin c.val.length)
    (hij : i<j) :
    ((before c ts i).flatMap labels).length+(ts i).labels.length≤((before c ts j).flatMap labels).length := by
  have h := (List.take_prefix_take_left (l := List.ofFn ts) (show i.val+1≤j.val by exact hij)).flatMap labels
  have he : (List.ofFn ts).take (i.val+1)=before c ts i++[ts i] := by
    rw [List.take_succ_eq_append_getElem (by simp)]
    simp only [before,List.getElem_ofFn]
  rw [he,List.flatMap_append,List.flatMap_singleton] at h
  simpa only [List.length_append,before] using h.length_le

lemma children_index_strict (c : Core) (ts : Fin c.val.length → CoreTree) (i j : Fin c.val.length)
    (hij : i<j) (v : (ts i).Node) (w : (ts j).Node) :
    (branch c ts).nodeIndex (.inr ⟨i,v⟩)<(branch c ts).nodeIndex (.inr ⟨j,w⟩) := by
  have hs := offset_separation c ts i j hij
  have hv := nodeIndex_bound (ts i) v
  simp only [nodeIndex]
  omega

lemma children_order (c : Core) (ts : Fin c.val.length → CoreTree)
    (i j : Fin c.val.length) (v : (ts i).Node) (w : (ts j).Node)
    (h : (branch c ts).nodeIndex (.inr ⟨i,v⟩)≤(branch c ts).nodeIndex (.inr ⟨j,w⟩)) : i≤j := by
  by_contra hn
  have hh := children_index_strict c ts j i (lt_of_not_ge hn) w v
  omega

lemma nodeIndex_root (t : CoreTree) : t.nodeIndex t.root=0 := by cases t <;> rfl

/-- The literal recursive node index covers every and only preorder cell. -/
lemma nodeIndex_surjective (t : CoreTree) {r : ℕ} (hr : r<t.labels.length) :
    ∃ v : t.Node,t.nodeIndex v=r := by
  induction t generalizing r with
  | leaf => exact ⟨leaf.root,by simp only [labels,List.length_singleton] at hr;simpa [nodeIndex_root] using (show 0=r by omega)⟩
  | branch c ts ih =>
    by_cases hr0 : r=0
    · exact ⟨.inl PUnit.unit,hr0.symm⟩
    · have hf : r-1<((List.ofFn ts).flatMap labels).length := by rw [labels_branch] at hr;simp only [List.length_cons] at hr;omega
      obtain ⟨i,j,hj,he⟩ := flatMap_find_index labels (List.ofFn ts) hf
      let k : Fin c.val.length := ⟨i.val,by simpa only [List.length_ofFn] using i.isLt⟩
      have hk : (List.ofFn ts)[i.val]=ts k := by simp [k]
      rw [hk] at hj
      obtain ⟨v,hv⟩ := ih k hj
      refine ⟨.inr ⟨k,v⟩,?_⟩
      dsimp only [nodeIndex,before,k]
      rw [hv]
      omega

end FKCRT.Inventory.CoreTree
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_CornerMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

lemma nodeIndex_injective (t : CoreTree) : Function.Injective t.nodeIndex := by
  induction t with
  | leaf => intro v w _; exact @Subsingleton.elim PUnit _ v w
  | branch c ts ih =>
    intro v w h
    cases v with
    | inl a =>
      cases w with
      | inl b => exact congrArg Sum.inl (Subsingleton.elim _ _)
      | inr w => simp only [nodeIndex] at h;omega
    | inr v =>
      obtain ⟨i,v⟩ := v
      cases w with
      | inl a => simp only [nodeIndex] at h;omega
      | inr w =>
        obtain ⟨j,w⟩ := w
        have hij := le_antisymm (children_order c ts i j v w h.le)
          (children_order c ts j i w v h.ge)
        subst j
        have hvw := ih i (show (ts i).nodeIndex v=(ts i).nodeIndex w by
          simpa only [nodeIndex,Nat.add_left_cancel_iff] using h)
        subst w
        rfl

/-- The literal preorder indexing is an equivalence, including the root. -/
def nodeEquiv (t : CoreTree) : t.Node ≃ Fin t.labels.length :=
  Equiv.ofBijective (fun v => ⟨t.nodeIndex v,t.nodeIndex_bound v⟩)
    ⟨fun _ _ h => t.nodeIndex_injective (congrArg Fin.val h),fun i => by
      obtain ⟨v,hv⟩ := t.nodeIndex_surjective i.isLt
      exact ⟨v,Fin.ext hv⟩⟩

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

/-- Preorder nodes indexed at the true total word length. -/
def wordNodeEquiv (t : CoreTree) : t.Node ≃ Fin (t.word.length+1) :=
  t.nodeEquiv.trans (finCongr t.labels_length)

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Equiv Equiv.Perm MeasureTheory
open scoped BigOperators ENNReal
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

def realizedPole (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n) (v : t.Node) : FKCRT.Vertex M :=
  ((t.pole v).map (fun d => orbit (FKCRT.rotation M) (e d))).getD (orbit (FKCRT.rotation M) 0)

def nonrootVertex (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n) (i : Fin t.word.length) : FKCRT.Vertex M :=
  t.realizedPole M e (t.wordNodeEquiv.symm i.succ)

end FKCRT.Inventory.CoreTree
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_FiniteLaw
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open List Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT
open Inventory TreeCoding
attribute [local instance] Classical.propDecidable

namespace Inventory.CoreTree

def sizedListEquiv (N : ℕ) : SizedWord N ≃ {w // w∈typedEmptyWords N} where
  toFun w := ⟨w.val.val,Finset.mem_filter.mpr ⟨mem_wordsOfLength.mpr w.property,w.val.property⟩⟩
  invFun w := ⟨⟨w.val,(Finset.mem_filter.mp w.property).2⟩,
    mem_wordsOfLength.mp (Finset.mem_filter.mp w.property).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

def successfulMarkedEquiv (n : ℕ) : SuccessfulWord n ≃ MarkedCode (2*(n+1)+1) :=
  ((successfulListEquiv n).trans (sizedListEquiv (2*(n+1))).symm).trans
    (markedWordEquiv (2*(n+1))).symm

end Inventory.CoreTree

end FKCRT
end


noncomputable section
open List Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT
open Inventory TreeCoding
attribute [local instance] Classical.propDecidable

/-- Evaluate precisely the original all-edge metric and degree measure of
an actual compatible marked core tree. Incompatible marks have probability
zero, and are assigned zero only to totalize an observable. -/
def markedMapTest (scale : ℝ) (n : ℕ) (F : MetricMeasureData → ℝ)
    (x : Code (2*(n+1)+1) × (Fin (2*(n+1)+1) → CoreLabel)) : ℝ :=
  if h : ∀ i,(x.2 i).arity=(x.1.val i).val then
    F (mapSpace scale ((rootedWordEquiv n).symm
      ((CoreTree.successfulMarkedEquiv n).symm ⟨x,h⟩)).1)
  else 0

end FKCRT
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_MeasuredCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open List Equiv Equiv.Perm MeasureTheory Set
open scoped BigOperators ENNReal
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

/-- The exact degree-mass coding, using every nonroot preorder pole. -/
def timeVertex (t : CoreTree) {n : ℕ} (M : FKCRT.RootedMap n)
    (e : t.Dart ≃ FKCRT.Dart n) (ht : 0<t.word.length) (s : unitInterval) : FKCRT.Vertex M :=
  t.nonrootVertex M e (FKCRT.timeCell t.word.length ht s)

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Equiv Equiv.Perm MeasureTheory Set
open scoped BigOperators ENNReal
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

/-- Same-code positive mesh, with the omitted root still present at time zero. -/
def nodePoint (t : CoreTree) (v : t.Node) : unitInterval :=
  ⟨((t.wordNodeEquiv v).val:ℝ)/(t.word.length+1:ℝ),by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      exact_mod_cast (t.wordNodeEquiv v).isLt.le⟩

end FKCRT.Inventory.CoreTree
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_GHPBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

/-- Actual normalized preorder height path, including both endpoint cells. -/
def heightCode {N : ℕ} (p : CriticalEvenOffspring) (d : Code N) : C(unitInterval,ℝ) :=
  interpolation N (fun i => p.sigma*height d.val i.val/(2*Real.sqrt N))

end FKCRT.TreeCoding
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_MetricLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
namespace FKCRT.Inventory
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

/-- The positive source normalization in original edge units. -/
def crtScale (P : Parameters) : ℝ := (actualOffspring P).sigma/(2*Real.sqrt 2*metricMean P)

def edgeScale (P : Parameters) (n : ℕ) : ℝ := crtScale P/Real.sqrt ((n:ℝ)+1)

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open FKCRT.TreeCoding
abbrev actualDrawLaw (P : Parameters) (n : ℕ) : Measure (ActualDraw n) :=
  (actualOffspring P).markedCodeLaw (fun k => (CoreLabel.markLaw P k).toMeasure) (n+1)
def actualHeight (P : Parameters) (n : ℕ) (x : ActualDraw n) : C(unitInterval,ℝ) :=
  heightFactor n • heightCode (actualOffspring P) x.1

end FKCRT.Inventory
end


noncomputable section
open List Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology NNReal
namespace FKCRT.Inventory
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

/-- All and only the three exceptional events needed for the original map
comparison: impossible marks (a null set), a macroscopic core, and a large
uniform ancestral distance error. -/
def metricBad (P : Parameters) (n : ℕ) (a : ℝ) : Set (ActualDraw n) :=
  {x | ¬∀ i,(x.2 i).arity=(x.1.val i).val} ∪
  {x | ∃ h : ∀ i,(x.2 i).arity=(x.1.val i).val,
    a*Real.sqrt ((2*(n+1)+1:ℕ):ℝ)<((CoreTree.ofMarkedCode ⟨x,h⟩).maxDegree:ℝ)} ∪
  {x | ∃ j : Fin (2*(n+1)+1),a*Real.sqrt ((2*(n+1)+1:ℕ):ℝ) <
    |markedSpineSum coreIncrement x.1 j.isLt.le x.2-metricMean P*height x.1.val j.val|}

end FKCRT.Inventory
end

end OAI
end


