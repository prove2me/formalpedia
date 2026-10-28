-- Prove2me | Definitions.Def_OAIW2GF000
-- name    : OAIW2GF000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T03:54:23.227578+00:00
-- url     : https://prove2.me/theorems/35a06d99-a6ff-4782-a194-7fc90ce4d6a2
-- title:
--   Definitions bundle OAIW2GF000 of the split of OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.GammaFPP.gamma_differentiability`, carved from OpenAI's openai/math development (OpenAI, *Strict convexity and differentiability of the planar exponential first-passage limit shape*, OpenAI Math Release, September 24, 2026, result family 212, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 445 declarations of OpenAI's Lean: 253 definitions, 2 inductive types or structures, 6 instances and 184 theorems. The definitions and types are `OAI.CompanionFPP.clipReal`, `OAI.CompanionFPP.coordinateVariance`, `OAI.CompanionFPP.exchangeCoordinate`, `OAI.GammaFPP.Analytic.NoCornerWedge`, `OAI.GammaFPP.Analytic.directionRatio`, `OAI.GammaFPP.Analytic.sphereChart`, `OAI.GammaFPP.Analytic.swapPlane`, `OAI.GammaFPP.BK.BitGood`, `OAI.GammaFPP.BK.RoundedDisjoint`, `OAI.GammaFPP.BK.RoundedGood`, `OAI.GammaFPP.BK.StrictDisjointPaths`, `OAI.GammaFPP.BK.StrictPathEvent`, `OAI.GammaFPP.BK.StrictPathWitness`, `OAI.GammaFPP.BK.StrictPathWitness.Good`, `OAI.GammaFPP.BK.StrictPathWitness.bits`, `OAI.GammaFPP.BK.StrictPathWitness.edges`, `OAI.GammaFPP.BK.bitDisjointFamily`, `OAI.GammaFPP.BK.bitFamily`, `OAI.GammaFPP.BK.dyadicSurvival`, `OAI.GammaFPP.BK.pathEdges`, `OAI.GammaFPP.CrossingBridge.BoundedIndexSteps`, `OAI.GammaFPP.CrossingBridge.ColumnConnection`, `OAI.GammaFPP.CrossingBridge.DependsOnEdges`, `OAI.GammaFPP.CrossingBridge.FullSpatialChunk`, `OAI.GammaFPP.CrossingBridge.PathIn`, `OAI.GammaFPP.CrossingBridge.SpatialBadPath`, `OAI.GammaFPP.CrossingBridge.UniformShape`, `OAI.GammaFPP.CrossingBridge.allPairsRegionEvent`, `OAI.GammaFPP.CrossingBridge.arbitraryEndpointEvent`, `OAI.GammaFPP.CrossingBridge.blockLayer`, `OAI.GammaFPP.CrossingBridge.blockLevel`, `OAI.GammaFPP.CrossingBridge.blockRegion`, `OAI.GammaFPP.CrossingBridge.blockVertices`, `OAI.GammaFPP.CrossingBridge.blockX`, `OAI.GammaFPP.CrossingBridge.blockY`, `OAI.GammaFPP.CrossingBridge.boundedLocalizedEvent`, `OAI.GammaFPP.CrossingBridge.characteristicExponent`, `OAI.GammaFPP.CrossingBridge.characteristicLength`, `OAI.GammaFPP.CrossingBridge.chunkIndexTail`, `OAI.GammaFPP.CrossingBridge.chunkInterior` and 215 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `FirstPassage_CoordinateTails`, `FirstPassage_ExtremeSlopes`, `FirstPassage_PassageTime`, `FirstPassage_PathWitnesses`, `FirstPassage_Paths`, `FirstPassage_PlaneGeometry`, `FirstPassage_ProbabilityFoundations`, `FirstPassage_Reversal`, `FirstPassage_SpatialModulus`, `FirstPassage_SupportContactEstimate`, `FirstPassage_Supports`, `FirstPassage_Translation`, `FirstPassage_WitnessDecomposition`, `GammaPassage_AnalyticCore`, `GammaPassage_AnalyticSpecialization`, `GammaPassage_BKBitLaw`, `GammaPassage_BKDyadic`, `GammaPassage_BKFamilies`, `GammaPassage_BKForcing`, `GammaPassage_BKPrimitives`, `GammaPassage_BKRepeated`, `GammaPassage_BKRounded`, `GammaPassage_BallTravelGeometry`, `GammaPassage_BoundaryGeometry`, `GammaPassage_BoundaryWinding`, `GammaPassage_CDF`, `GammaPassage_CharacteristicLengths`, `GammaPassage_CheapLongTrails`, `GammaPassage_CheapPathCounting`, `GammaPassage_CheapPathDecay`, `GammaPassage_ConcentrationScale`, `GammaPassage_ConnectorEvents`, `GammaPassage_ConnectorGeometry`, `GammaPassage_ContourEnumeration`, `GammaPassage_ContourLocalization`, `GammaPassage_CoordinateTails`, `GammaPassage_CrossingChain`, `GammaPassage_CrossingEvents`, `GammaPassage_CrossingLocalized`, `GammaPassage_DyadicRanks`, `GammaPassage_EndpointBounds`, `GammaPassage_EndpointCoarseGeometry`, `GammaPassage_EndpointConnection`, `GammaPassage_EndpointEvents`, `GammaPassage_EndpointExtensions`, `GammaPassage_EndpointGeometry`, `GammaPassage_EndpointMesh`, `GammaPassage_EndpointNet`, `GammaPassage_EndpointTail`, `GammaPassage_Environment`, `GammaPassage_FiniteEdgeTilt`, `GammaPassage_FiniteMoments`, `GammaPassage_FiniteTilt`, `GammaPassage_FirstMoment`, `GammaPassage_GlobalConcentration`, `GammaPassage_GoodSiteBlocks`, `GammaPassage_GoodSiteEvents`, `GammaPassage_GoodSiteTrials`, `GammaPassage_GridAttachments`, `GammaPassage_GridCounting`, `GammaPassage_GridEvents`, `GammaPassage_GridGeometry`, `GammaPassage_GridIndependence`, `GammaPassage_GridMeshes`, `GammaPassage_GridTail`, `GammaPassage_HighDensityOriented`, `GammaPassage_LocalResamplingModel`, `GammaPassage_LocalTrailCandidates`, `GammaPassage_LocalTrailPassage`, `GammaPassage_LoopErasure`, `GammaPassage_MeanAlgebra`, `GammaPassage_MeanLimit`, `GammaPassage_MeanLipschitz`, `GammaPassage_MeanNorm`, `GammaPassage_MeanPairSeminorm`, `GammaPassage_MeanSwap`, `GammaPassage_MovingOrigin`, `GammaPassage_OrientedCompactness`, `GammaPassage_OrientedProbability`, `GammaPassage_OrientedSelection`, `GammaPassage_OriginEscape`, `GammaPassage_PathIntegrability`, `GammaPassage_PathSecondMoment`, `GammaPassage_PathSubpaths`, `GammaPassage_Quantile`, `GammaPassage_RareFastEvents`, `GammaPassage_RationalMean`, `GammaPassage_RationalMeanAlgebra`, `GammaPassage_RealDirectionGeometry`, `GammaPassage_RealMeanExtension`, `GammaPassage_SequenceSummability`, `GammaPassage_ShapeDeficit`, `GammaPassage_ShortCrossingGeometry`, `GammaPassage_SourceConnector`, `GammaPassage_SourceTilt`, `GammaPassage_SpatialBadPathCover`, `GammaPassage_SpatialChunkGeometry`, `GammaPassage_SpatialChunks`, `GammaPassage_SpatialFirstExit`, `GammaPassage_SpatialModulus`, `GammaPassage_SpatialWitnesses`, `GammaPassage_SquareLoops`, `GammaPassage_Stationarity`, `GammaPassage_SurvivalQuantile`, `GammaPassage_SurvivalRounding`, `GammaPassage_TiltDensity`, `GammaPassage_TiltMoment`, `GammaPassage_TiltRegionCount`, `GammaPassage_TubeDeterministic`, `GammaPassage_UniformShapeGeometry`, `GammaPassage_Waypoints`, `GammaPassage_WitnessEntropy`, `GammaPassage_WitnessSelection`, `LatticePassage_EfronStein`, `LatticePassage_FiniteVariance`, `LatticePassage_ResamplingSymmetry`.
--
--   **Imports.** It imports the published bundle `Def_GammaPassage`.
--
--   **Imported by** (directly, in this split): the statements `OAI.GammaFPP.CrossingBridge.gamma_arbitraryEndpoint_tendsto_of_grids`, `OAI.GammaFPP.CrossingBridge.gamma_characteristic_lengths_exist`, `OAI.GammaFPP.CrossingBridge.gamma_direction_nat_limit`, `OAI.GammaFPP.CrossingBridge.gamma_goodSiteEvent_failure`, `OAI.GammaFPP.CrossingBridge.gamma_spatial_witness_BK_scales`, `OAI.GammaFPP.GammaEnvironment.ae_eventually_origin_escape`, `OAI.GammaFPP.GammaEnvironment.isTimeConstant`, `OAI.GammaFPP.GammaEnvironment.uniform_shape` and `OAI.GammaFPP.IntervalTravelBridge.gamma_moving_goodOrigin_failure_tendsto`; the proofs of `OAI.GammaFPP.CrossingBridge.gamma_arbitraryEndpoint_tendsto_of_grids`, `OAI.GammaFPP.CrossingBridge.gamma_characteristic_lengths_exist`, `OAI.GammaFPP.CrossingBridge.gamma_direction_nat_limit`, `OAI.GammaFPP.CrossingBridge.gamma_goodSiteEvent_failure`, `OAI.GammaFPP.CrossingBridge.gamma_spatial_witness_BK_scales`, `OAI.GammaFPP.GammaEnvironment.ae_eventually_origin_escape`, `OAI.GammaFPP.GammaEnvironment.isTimeConstant`, `OAI.GammaFPP.GammaEnvironment.uniform_shape`, `OAI.GammaFPP.IntervalTravelBridge.gamma_moving_goodOrigin_failure_tendsto` and `OAI.GammaFPP.gamma_differentiability`.
-- source:
--   OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 212; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_GammaPassage

section
-- module Solutions.OAIW2_GammaFPP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_Paths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

def Step.reverse : Step → Step
  | .east => .west
  | .west => .east
  | .north => .south
  | .south => .north

@[simp] theorem Step.delta_reverse (d : Step) : d.reverse.delta = -d.delta := by
  cases d <;> rfl

@[simp] theorem Step.edge_reverse (p : Vertex) (d : Step) :
    d.reverse.edge (p + d.delta) = d.edge p := by
  cases d <;> simp [Step.reverse, Step.edge, Step.delta, Prod.ext_iff]

@[simp] theorem displacement_nil : displacement [] = 0 := rfl
@[simp] theorem displacement_cons (d : Step) (ds : List Step) :
    displacement (d :: ds) = d.delta + displacement ds := by simp [displacement]
@[simp] theorem displacement_append (ds es : List Step) :
    displacement (ds ++ es) = displacement ds + displacement es := by
  simp [displacement]

theorem pathCost_append (τ : Edge → ℝ) (p : Vertex) (ds es : List Step) :
    pathCost τ p (ds ++ es) =
      pathCost τ p ds + pathCost τ (p + displacement ds) es := by
  induction ds generalizing p with
  | nil => simp [pathCost]
  | cons d ds ih => simp [pathCost, ih, add_assoc]

theorem pathCost_nonneg {τ : Edge → ℝ} (hτ : ∀ e, 0 ≤ τ e)
    (p : Vertex) (ds : List Step) : 0 ≤ pathCost τ p ds := by
  induction ds generalizing p with
  | nil => exact le_refl 0
  | cons d ds ih => exact add_nonneg (hτ _) (ih _)

noncomputable def transverse (b : ℝ) (z : Vertex) : ℝ := z.2 - b * z.1
noncomputable def support (b m a : ℝ) (z : Vertex) : ℝ := m * z.1 + a * transverse b z
noncomputable def defect (τ : Edge → ℝ) (b m a : ℝ) (p : Vertex) (ds : List Step) : ℝ :=
  pathCost τ p ds - support b m a (displacement ds)

@[simp] theorem transverse_add (b : ℝ) (z w : Vertex) :
    transverse b (z + w) = transverse b z + transverse b w := by
  simp [transverse]; ring
@[simp] theorem support_add (b m a : ℝ) (z w : Vertex) :
    support b m a (z + w) = support b m a z + support b m a w := by
  simp [support]; ring

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_PassageTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

def horizontal (n : ℤ) : List Step :=
  if 0 ≤ n then List.replicate n.toNat Step.east
  else List.replicate (-n).toNat Step.west

def vertical (n : ℤ) : List Step :=
  if 0 ≤ n then List.replicate n.toNat Step.north
  else List.replicate (-n).toNat Step.south

theorem displacement_horizontal (n : ℤ) : displacement (horizontal n) = (n, 0) := by
  by_cases hn : 0 ≤ n
  · simp [horizontal, hn, displacement, Step.delta,
      Int.toNat_of_nonneg hn]
  · have hn' : 0 ≤ -n := by omega
    simp [horizontal, hn, displacement, Step.delta,
      Int.toNat_of_nonneg hn']

theorem displacement_vertical (n : ℤ) : displacement (vertical n) = (0, n) := by
  by_cases hn : 0 ≤ n
  · simp [vertical, hn, displacement, Step.delta,
      Int.toNat_of_nonneg hn]
  · have hn' : 0 ≤ -n := by omega
    simp [vertical, hn, displacement, Step.delta,
      Int.toNat_of_nonneg hn']

theorem exists_path (p q : Vertex) : ∃ ds, p + displacement ds = q := by
  refine ⟨horizontal (q.1 - p.1) ++ vertical (q.2 - p.2), ?_⟩
  rw [displacement_append, displacement_horizontal, displacement_vertical]
  ext <;> simp

theorem path_costs_nonempty (τ : Edge → ℝ) (p q : Vertex) :
    {t | ∃ ds : List Step, p + displacement ds = q ∧ pathCost τ p ds = t}.Nonempty := by
  obtain ⟨ds, hds⟩ := exists_path p q
  exact ⟨pathCost τ p ds, ds, hds, rfl⟩

theorem path_costs_bddBelow (τ : Edge → ℝ) (hτ : ∀ e, 0 ≤ τ e) (p q : Vertex) :
    BddBelow {t | ∃ ds : List Step, p + displacement ds = q ∧ pathCost τ p ds = t} := by
  refine ⟨0, ?_⟩
  rintro t ⟨ds, _, rfl⟩
  exact pathCost_nonneg hτ p ds

theorem passageTime_nonneg (τ : Edge → ℝ) (hτ : ∀ e, 0 ≤ τ e) (p q : Vertex) :
    0 ≤ passageTime τ p q := by
  apply le_csInf (path_costs_nonempty τ p q)
  rintro t ⟨ds, _, rfl⟩
  exact pathCost_nonneg hτ p ds

theorem passageTime_le_cost (τ : Edge → ℝ) (hτ : ∀ e, 0 ≤ τ e)
    (p q : Vertex) (ds : List Step) (hend : p + displacement ds = q) :
    passageTime τ p q ≤ pathCost τ p ds :=
  csInf_le (path_costs_bddBelow τ hτ p q) ⟨ds, hend, rfl⟩

theorem exists_near_optimal_path (τ : Edge → ℝ) (p q : Vertex)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ds : List Step, p + displacement ds = q ∧
      pathCost τ p ds < passageTime τ p q + ε := by
  obtain ⟨t, ⟨ds, hend, hcost⟩, ht⟩ :=
    exists_lt_of_csInf_lt (path_costs_nonempty τ p q)
      (show sInf {t | ∃ ds : List Step, p + displacement ds = q ∧ pathCost τ p ds = t}
        < passageTime τ p q + ε by change passageTime τ p q < _; linarith)
  exact ⟨ds, hend, by simpa [hcost] using ht⟩

theorem passageTime_triangle (τ : Edge → ℝ) (hτ : ∀ e, 0 ≤ τ e) (p q r : Vertex) :
    passageTime τ p r ≤ passageTime τ p q + passageTime τ q r := by
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨ds, hd, hdc⟩ := exists_near_optimal_path τ p q (ε / 2) (by linarith)
  obtain ⟨es, he, hec⟩ := exists_near_optimal_path τ q r (ε / 2) (by linarith)
  have hfinish : p + displacement (ds ++ es) = r := by
    rw [displacement_append, ← add_assoc, hd, he]
  have hc := passageTime_le_cost τ hτ p r (ds ++ es) hfinish
  rw [pathCost_append, hd] at hc
  linarith

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_ProbabilityFoundations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set Filter

instance instCountableStep : Countable Step := by
  let code : Step → ℕ := fun d => match d with
    | .east => 0 | .west => 1 | .north => 2 | .south => 3
  have hi : Function.Injective code := by
    intro d e h
    cases d <;> cases e <;> simp_all [code]
  exact hi.countable

noncomputable instance rateOneProbability : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem measurable_pathCost (hτ : ∀ e, Measurable (τ e))
    (p : Vertex) (ds : List Step) :
    Measurable (fun ω => pathCost (fun e => τ e ω) p ds) := by
  induction ds generalizing p with
  | nil => exact measurable_const
  | cons d ds ih => exact (hτ _).add (ih _)

theorem measurable_passageTime (hτ : ∀ e, Measurable (τ e)) (p q : Vertex) :
    Measurable (fun ω => passageTime (fun e => τ e ω) p q) := by
  have hm := Measurable.sInf (Set.to_countable {ds : List Step |
    p + displacement ds = q}) (fun ds _ => measurable_pathCost hτ p ds)
  convert hm using 1
  funext ω
  unfold passageTime
  congr 1

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_Reversal
attribute [-instance] _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

def reverseSteps (ds : List Step) : List Step := ds.reverse.map Step.reverse

@[simp] theorem reverseSteps_nil : reverseSteps [] = [] := rfl
@[simp] theorem reverseSteps_cons (d : Step) (ds : List Step) :
    reverseSteps (d :: ds) = reverseSteps ds ++ [d.reverse] := by
  simp [reverseSteps]

@[simp] theorem displacement_reverseSteps (ds : List Step) :
    displacement (reverseSteps ds) = -displacement ds := by
  induction ds with
  | nil => simp
  | cons d ds ih => simp [ih, add_comm]

theorem pathCost_reverse (τ : Edge → ℝ) (p : Vertex) (ds : List Step) :
    pathCost τ (p + displacement ds) (reverseSteps ds) = pathCost τ p ds := by
  induction ds generalizing p with
  | nil => simp [pathCost]
  | cons d ds ih =>
    rw [reverseSteps_cons, displacement_cons, pathCost_append]
    have ha : p + (d.delta + displacement ds) = (p + d.delta) + displacement ds :=
      (add_assoc _ _ _).symm
    rw [ha, ih, displacement_reverseSteps]
    have hb : p + d.delta + displacement ds + -displacement ds = p + d.delta := by
      simp [add_assoc]
    rw [hb]
    simp [pathCost, Step.edge_reverse, add_comm]

theorem passageTime_symm (τ : Edge → ℝ) (hτ : ∀ e, 0 ≤ τ e) (p q : Vertex) :
    passageTime τ p q = passageTime τ q p := by
  have hle : ∀ p q, passageTime τ p q ≤ passageTime τ q p := by
    intro p q
    apply le_csInf (path_costs_nonempty τ q p)
    rintro t ⟨ds, hend, rfl⟩
    have hfinish : p + displacement (reverseSteps ds) = q := by
      rw [displacement_reverseSteps, ← hend]
      simp [add_assoc]
    have hc := passageTime_le_cost τ hτ p q (reverseSteps ds) hfinish
    rw [← hend, pathCost_reverse] at hc
    simpa only [hend] using hc
  exact le_antisymm (hle p q) (hle q p)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_CoordinateTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

def straightEdge (p : Vertex) (d : Step) (i : ℕ) : Edge :=
  d.edge (p + (i : ℤ) • d.delta)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

def coordinatePath (p q : Vertex) : List Step :=
  horizontal (q.1 - p.1) ++ vertical (q.2 - p.2)

def latticeDistance (p q : Vertex) : ℕ :=
  (q.1 - p.1).natAbs + (q.2 - p.2).natAbs

theorem coordinatePath_endpoint (p q : Vertex) : p + displacement (coordinatePath p q) = q := by
  simp [coordinatePath, displacement_horizontal, displacement_vertical, Prod.ext_iff]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_Supports
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

noncomputable def coordinateSupport (x r : E →ₗ[ℝ] ℝ) (m a : ℝ) : E →ₗ[ℝ] ℝ :=
  m • x + a • r

@[simp] theorem coordinateSupport_apply (x r : E →ₗ[ℝ] ℝ) (m a : ℝ) (z : E) :
    coordinateSupport x r m a z = m * x z + a * r z := rfl

end
end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_ExtremeSlopes
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

noncomputable def leftSlope (φ : ℝ → ℝ) : ℝ := derivWithin φ (Iio 0) 0
noncomputable def rightSlope (φ : ℝ → ℝ) : ℝ := derivWithin φ (Ioi 0) 0

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_WitnessDecomposition
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

variable {α : Type*}

noncomputable def total (d : α → ℝ) (xs : List α) : ℝ := (xs.map d).sum
@[simp] theorem total_nil (d : α → ℝ) : total d [] = 0 := rfl
@[simp] theorem total_cons (d : α → ℝ) (x : α) (xs : List α) :
    total d (x :: xs) = d x + total d xs := by simp [total]
@[simp] theorem total_append (d : α → ℝ) (xs ys : List α) :
    total d (xs ++ ys) = total d xs + total d ys := by simp [total]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_PathWitnesses
attribute [-instance] _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

abbrev Traversal := Vertex × Step

def traversalEdge (t : Traversal) : Edge := t.2.edge t.1

def trace (p : Vertex) : List Step → List Traversal
  | [] => []
  | d :: ds => (p, d) :: trace (p + d.delta) ds

noncomputable def stepDefect (τ : Edge → ℝ) (b m a : ℝ) (t : Traversal) : ℝ :=
  τ (traversalEdge t) - support b m a t.2.delta

@[simp] theorem support_zero (b m a : ℝ) : support b m a 0 = 0 := by
  simp [support, transverse]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_PlaneGeometry
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

noncomputable def direction (b : ℝ) : Plane := WithLp.toLp 2 ![1, b]
noncomputable def transverseUnit : Plane := WithLp.toLp 2 ![0, 1]
noncomputable def xCoord : Plane →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0
noncomputable def rCoord (b : ℝ) : Plane →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1 - b • xCoord

@[simp] theorem xCoord_apply (z : Plane) : xCoord z = z 0 := rfl
@[simp] theorem rCoord_apply (b : ℝ) (z : Plane) : rCoord b z = z 1 - b * z 0 := rfl
@[simp] theorem xCoord_direction (b : ℝ) : xCoord (direction b) = 1 := rfl
@[simp] theorem rCoord_direction (b : ℝ) : rCoord b (direction b) = 0 := by
  simp [rCoord_apply, direction]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_SpatialModulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Finset Filter Set
open scoped ENNReal Topology

noncomputable def latticeBox (n : ℕ) : Finset Vertex :=
  (Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (-(n : ℤ)) n)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_SupportContactEstimate
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter
open scoped Topology

noncomputable def extremeSlope (μ : Plane → ℝ) (b : ℝ) (plus : Bool) : ℝ :=
  if plus then rightSlope (fun t => μ (direction b+t • transverseUnit))
  else leftSlope (fun t => μ (direction b+t • transverseUnit))

def contactSide (plus : Bool) : Set ℝ := if plus then Ioi 0 else Iio 0

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_Translation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set

def shiftEdge (a : Vertex) (e : Edge) : Edge := (a+e.1,e.2)

theorem shiftEdge_injective (a : Vertex) : Function.Injective (shiftEdge a) := by
  intro e f h
  simpa [shiftEdge, Prod.ext_iff] using h

theorem step_edge_translate (a p : Vertex) (d : Step) :
    d.edge (a+p) = shiftEdge a (d.edge p) := by
  cases d <;> simp [Step.edge, shiftEdge, add_assoc]

theorem pathCost_translate (w : Edge → ℝ) (a p : Vertex) (ds : List Step) :
    pathCost (fun e => w (shiftEdge a e)) p ds = pathCost w (a+p) ds := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp [pathCost, step_edge_translate, ih, add_assoc]

theorem passageTime_translate (w : Edge → ℝ) (a p q : Vertex) :
    passageTime (fun e => w (shiftEdge a e)) p q = passageTime w (a+p) (a+q) := by
  unfold passageTime
  congr 1
  ext t
  simp only [mem_ofPred_eq, pathCost_translate, add_assoc, add_left_cancel_iff]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_Environment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory

/-- The product law of the edge weights. -/
noncomputable def iidProductLaw (ν : Measure ℝ) : Measure (PlanarFPP.Edge → ℝ) :=
  Measure.infinitePi (fun _ : PlanarFPP.Edge => ν)

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ν : Measure ℝ} {P : Measure Ω} {τ : PlanarFPP.Edge → Ω → ℝ}

/-- Passage time is measurable in an iid edge environment. -/
theorem IidEnvironment.measurable_passageTime (h : IidEnvironment ν P τ)
    (p q : PlanarFPP.Vertex) :
    Measurable (fun ω => PlanarFPP.passageTime (fun e => τ e ω) p q) :=
  PlanarFPP.measurable_passageTime h.measurable p q

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_AnalyticCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.Analytic
open PlanarFPP Set Filter MeasureTheory
open scoped Topology
noncomputable def swapPlane : Plane ≃ₗᵢ[ℝ] Plane :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 1)

@[simp] lemma swapPlane_zero (v : Plane) : swapPlane v 0=v 1 := by
  simp [swapPlane,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']
@[simp] lemma swapPlane_one (v : Plane) : swapPlane v 1=v 0 := by
  simp [swapPlane,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']
@[simp] lemma swapPlane_swap (v : Plane) : swapPlane (swapPlane v)=v := by
  ext i; fin_cases i <;> simp

noncomputable def sphereChart (μ : Plane → ℝ) (c t : ℝ) : Plane :=
  (c/μ (direction t)) • direction t
noncomputable def directionRatio (v : Plane) : ℝ := v 1/v 0

end GammaFPP.Analytic

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_FirstMoment
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

/-- The Gamma law is concentrated on strictly positive real weights. -/
theorem gamma_ae_pos (shape rate : ℝ) :
    ∀ᵐ x : ℝ ∂gammaMeasure shape rate, 0 < x := by
  change ∀ᵐ x : ℝ ∂volume.withDensity (gammaPDF shape rate), 0 < x
  rw [ae_withDensity_iff (by unfold gammaPDF; fun_prop)]
  filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
  intro hd
  by_contra h
  exact hd (gammaPDF_of_neg (lt_of_le_of_ne (le_of_not_gt h) hx))

/-- Multiplication by `x` shifts the Gamma shape by one. Both sides vanish at the origin. -/
lemma gamma_first_weighted_density {shape rate : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (x : ℝ) :
    gammaPDF shape rate x * ENNReal.ofReal x =
      ENNReal.ofReal (shape / rate) * gammaPDF (shape + 1) rate x := by
  by_cases hx : 0 < x
  · rw [gammaPDF_of_nonneg hx.le, gammaPDF_of_nonneg hx.le,
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (div_pos hshape hrate).le]
    congr 1
    have hxp : x ^ (shape - 1) * x = x ^ shape := by
      calc
        x ^ (shape - 1) * x = x ^ (shape - 1) * x ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = x ^ shape := by
          rw [← Real.rpow_add hx]
          congr 1
          ring
    rw [Real.Gamma_add_one hshape.ne', Real.rpow_add hrate, Real.rpow_one]
    simp only [add_sub_cancel_right]
    calc
      rate ^ shape / Gamma shape * x ^ (shape - 1) * exp (-(rate * x)) * x =
          rate ^ shape / Gamma shape * (x ^ (shape - 1) * x) *
            exp (-(rate * x)) := by ring
      _ = rate ^ shape / Gamma shape * x ^ shape * exp (-(rate * x)) := by rw [hxp]
      _ = shape / rate *
          (rate ^ shape * rate / (shape * Gamma shape) * x ^ shape *
            exp (-(rate * x))) := by
        field_simp [hrate.ne', hshape.ne', (Real.Gamma_pos_of_pos hshape).ne']
  · rcases lt_or_eq_of_le (le_of_not_gt hx) with hn | rfl
    · simp [gammaPDF_of_neg hn, ENNReal.ofReal_eq_zero.mpr hn.le]
    · simp [gammaPDF, gammaPDFReal, Real.zero_rpow hshape.ne']

/-- The nonnegative first moment from the normalized density with shifted shape. -/
theorem gamma_lintegral_id {shape rate : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) :
    (∫⁻ x : ℝ, ENNReal.ofReal x ∂gammaMeasure shape rate) =
      ENNReal.ofReal (shape / rate) := by
  change (∫⁻ x : ℝ, ENNReal.ofReal x
    ∂volume.withDensity (gammaPDF shape rate)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume
    (by unfold gammaPDF; fun_prop) (by fun_prop)]
  simp only [Pi.mul_apply, gamma_first_weighted_density hshape hrate]
  rw [lintegral_const_mul _ (by unfold gammaPDF; fun_prop),
    lintegral_gammaPDF_eq_one (by linarith : 0 < shape + 1) hrate, mul_one]

/-- The Gamma law has an integrable identity function for positive shape and rate. -/
theorem gamma_integrable_id {shape rate : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) :
    Integrable (fun x : ℝ => x) (gammaMeasure shape rate) := by
  apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    ((gamma_ae_pos shape rate).mono fun _ hx => hx.le)).mp
  rw [gamma_lintegral_id hshape hrate]
  exact ENNReal.ofReal_ne_top

/-- The mean of the Gamma law with shape and rate parameters. -/
theorem gamma_integral_id {shape rate : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) :
    (∫ x : ℝ, x ∂gammaMeasure shape rate) = shape / rate := by
  rw [integral_eq_lintegral_of_nonneg_ae
    ((gamma_ae_pos shape rate).mono fun _ hx => hx.le) (by fun_prop),
    gamma_lintegral_id hshape hrate]
  exact ENNReal.toReal_ofReal (div_pos hshape hrate).le
end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_PathIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Set Filter

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : PlanarFPP.Edge → Ω → ℝ}
variable {shape rate : ℝ}

/-- All edge weights are almost surely positive, by positivity of the marginal and countability. -/
theorem GammaEnvironment.ae_positive (h : GammaEnvironment shape rate P τ) :
    ∀ᵐ ω ∂P, ∀ e, 0 < τ e ω := by
  rw [ae_all_iff]
  intro e
  have hp : ∀ᵐ x ∂Measure.map (τ e) P, 0 < x := by
    rw [h.marginal e]
    exact gamma_ae_pos shape rate
  exact (ae_map_iff (h.measurable e).aemeasurable measurableSet_Ioi).mp hp

/-- Each Gamma edge weight is integrable. -/
theorem GammaEnvironment.integrable_edge (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (e : PlanarFPP.Edge) :
    Integrable (τ e) P := by
  have hi : Integrable (fun x : ℝ => x) (Measure.map (τ e) P) := by
    rw [h.marginal e]
    exact gamma_integrable_id hs hr
  simpa only [Function.comp_def] using hi.comp_aemeasurable (h.measurable e).aemeasurable

/-- The mean edge weight is `shape / rate`. -/
theorem GammaEnvironment.integral_edge (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (e : PlanarFPP.Edge) :
    (∫ ω, τ e ω ∂P) = shape / rate := by
  have he : (∫ x : ℝ, x ∂Measure.map (τ e) P) = ∫ ω, τ e ω ∂P :=
    integral_map (h.measurable e).aemeasurable measurable_id.aestronglyMeasurable
  rw [h.marginal e, gamma_integral_id hs hr] at he
  exact he.symm

/-- The cost of a fixed finite step list is integrable, including repeated edges. -/
theorem GammaEnvironment.integrable_pathCost (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (p : PlanarFPP.Vertex) (ds : List PlanarFPP.Step) :
    Integrable (fun ω => PlanarFPP.pathCost (fun e => τ e ω) p ds) P := by
  induction ds generalizing p with
  | nil =>
      let : IsProbabilityMeasure P := h.probability
      change Integrable (fun _ : Ω => (0 : ℝ)) P
      exact integrable_const (μ := P) (0 : ℝ)
  | cons d ds ih =>
      exact (h.integrable_edge hs hr (d.edge p)).add (ih (p + d.delta))

/-- Expected path cost counts edge traversals. The empty path has expectation zero. -/
theorem GammaEnvironment.integral_pathCost (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (p : PlanarFPP.Vertex) (ds : List PlanarFPP.Step) :
    (∫ ω, PlanarFPP.pathCost (fun e => τ e ω) p ds ∂P) =
      (ds.length : ℝ) * (shape / rate) := by
  induction ds generalizing p with
  | nil => simp [PlanarFPP.pathCost]
  | cons d ds ih =>
      change (∫ ω, τ (d.edge p) ω +
        PlanarFPP.pathCost (fun e => τ e ω) (p + d.delta) ds ∂P) = _
      rw [integral_add (h.integrable_edge hs hr (d.edge p))
        (h.integrable_pathCost hs hr (p + d.delta) ds),
        h.integral_edge hs hr (d.edge p), ih]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring

/-- Passage time is integrable by domination by the cost of one deterministic path. -/
theorem GammaEnvironment.integrable_passageTime (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (p q : PlanarFPP.Vertex) :
    Integrable (fun ω => PlanarFPP.passageTime (fun e => τ e ω) p q) P := by
  obtain ⟨ds, hend⟩ := PlanarFPP.exists_path p q
  apply (h.integrable_pathCost hs hr p ds).mono'
    (h.measurable_passageTime p q).aestronglyMeasurable
  filter_upwards [h.ae_positive] with ω hω
  have hn : ∀ e, 0 ≤ τ e ω := fun e => (hω e).le
  rw [Real.norm_eq_abs, abs_of_nonneg (PlanarFPP.passageTime_nonneg _ hn p q)]
  exact PlanarFPP.passageTime_le_cost _ hn p q ds hend

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_Stationarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {ν : Measure ℝ}

/-- Deterministic lattice translation preserves an iid environment. -/
theorem IidEnvironment.translate (h : IidEnvironment ν P τ) (a : Vertex) :
    IidEnvironment ν P (fun e => τ (shiftEdge a e)) where
  probability := h.probability
  measurable := fun e => h.measurable (shiftEdge a e)
  independent := h.independent.precomp (shiftEdge_injective a)
  marginal := fun e => h.marginal (shiftEdge a e)

/-- The complete configuration has the product law. -/
theorem IidEnvironment.jointLaw (h : IidEnvironment ν P τ) :
    Measure.map (fun ω e => τ e ω) P = iidProductLaw ν := by
  rw [h.independent.map_fun_eq_infinitePi_map h.measurable]
  simp only [h.marginal, iidProductLaw]

/-- Integral transport to the common product law. -/
theorem IidEnvironment.integral_configuration (h : IidEnvironment ν P τ)
    (f : (Edge → ℝ) → ℝ) (hf : Measurable f) :
    (∫ ω, f (fun e => τ e ω) ∂P) = ∫ w, f w ∂iidProductLaw ν := by
  rw [← h.jointLaw]
  exact (integral_map (Measurable.of_eval h.measurable).aemeasurable
    hf.aestronglyMeasurable).symm

/-- Translated passage times have equal expectations. -/
theorem IidEnvironment.integral_passageTime_translate
    (h : IidEnvironment ν P τ) (a p q : Vertex) :
    (∫ ω, passageTime (fun e => τ e ω) (a + p) (a + q) ∂P) =
      ∫ ω, passageTime (fun e => τ e ω) p q ∂P := by
  have hm : Measurable (fun w : Edge → ℝ => passageTime w p q) :=
    PlanarFPP.measurable_passageTime (fun e => measurable_pi_apply e) p q
  have ht := (h.translate a).integral_configuration
    (fun w : Edge → ℝ => passageTime w p q) hm
  have ho := h.integral_configuration (fun w : Edge → ℝ => passageTime w p q) hm
  have he : (∫ ω, passageTime (fun e => τ e ω) (a + p) (a + q) ∂P) =
      ∫ ω, passageTime (fun e => τ (shiftEdge a e) ω) p q ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      (passageTime_translate (fun e => τ e ω) a p q).symm)
  exact he.trans (ht.trans ho.symm)

variable {shape rate : ℝ}

/-- The expected passage time is nonnegative. -/
theorem GammaEnvironment.integral_passageTime_nonneg
    (h : GammaEnvironment shape rate P τ) (p q : Vertex) :
    0 ≤ ∫ ω, passageTime (fun e => τ e ω) p q ∂P := by
  apply integral_nonneg_of_ae
  filter_upwards [h.ae_positive] with ω hω
  exact passageTime_nonneg _ (fun e => (hω e).le) p q

/-- A deterministic path bounds the expected passage time, counting every traversal. -/
theorem GammaEnvironment.integral_passageTime_le_path_length
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (ds : List Step) (hend : p + displacement ds = q) :
    (∫ ω, passageTime (fun e => τ e ω) p q ∂P) ≤
      (ds.length : ℝ) * (shape / rate) := by
  have hb := integral_mono_ae (h.integrable_passageTime hs hr p q)
    (h.integrable_pathCost hs hr p ds) (by
      filter_upwards [h.ae_positive] with ω hω
      exact passageTime_le_cost _ (fun e => (hω e).le) p q ds hend)
  rw [h.integral_pathCost hs hr p ds] at hb
  exact hb

/-- Stationarity and the passage-time triangle inequality give subadditivity in expectation. -/
theorem GammaEnvironment.mean_passageTime_subadditive
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (x y : Vertex) :
    (∫ ω, passageTime (fun e => τ e ω) 0 (x + y) ∂P) ≤
      (∫ ω, passageTime (fun e => τ e ω) 0 x ∂P) +
      (∫ ω, passageTime (fun e => τ e ω) 0 y ∂P) := by
  have hb := integral_mono_ae (h.integrable_passageTime hs hr 0 (x + y))
    ((h.integrable_passageTime hs hr 0 x).add
      (h.integrable_passageTime hs hr x (x + y))) (by
        filter_upwards [h.ae_positive] with ω hω
        exact passageTime_triangle _ (fun e => (hω e).le) 0 x (x + y))
  simp only [Pi.add_apply] at hb
  rw [integral_add (h.integrable_passageTime hs hr 0 x)
    (h.integrable_passageTime hs hr x (x + y))] at hb
  have ht := h.integral_passageTime_translate x 0 y
  simp only [add_zero] at ht
  rw [ht] at hb
  exact hb

/-- Mean passage time along an integer lattice direction, indexed by natural steps. -/
noncomputable def meanPassageSequence (P : Measure Ω) (τ : Edge → Ω → ℝ)
    (z : Vertex) (n : ℕ) : ℝ :=
  ∫ ω, passageTime (fun e => τ e ω) 0 (n • z) ∂P

theorem GammaEnvironment.meanPassageSequence_nonneg
    (h : GammaEnvironment shape rate P τ) (z : Vertex) (n : ℕ) :
    0 ≤ meanPassageSequence P τ z n :=
  h.integral_passageTime_nonneg 0 (n • z)

/-- Subadditivity includes the zero direction and zero indices. -/
theorem GammaEnvironment.meanPassageSequence_subadditive
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) (m n : ℕ) :
    meanPassageSequence P τ z (m + n) ≤
      meanPassageSequence P τ z m + meanPassageSequence P τ z n := by
  unfold meanPassageSequence
  rw [add_nsmul]
  exact h.mean_passageTime_subadditive hs hr (m • z) (n • z)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MeanLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory Filter Topology PlanarFPP

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Mean passage times along a lattice ray form a subadditive sequence. -/
theorem GammaEnvironment.meanPassageSequence_isSubadditive
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) : Subadditive (meanPassageSequence P τ z) := by
  intro m n
  exact h.meanPassageSequence_subadditive hs hr z m n

/-- Nonnegative passage times bound the normalized mean sequence below,
including the totalized quotient at `n = 0`. -/
theorem GammaEnvironment.normalized_meanPassage_bddBelow
    (h : GammaEnvironment shape rate P τ) (z : Vertex) :
    BddBelow (Set.range (fun n : ℕ => meanPassageSequence P τ z n / (n : ℝ))) := by
  refine ⟨0, ?_⟩
  rintro r ⟨n, rfl⟩
  exact div_nonneg (h.meanPassageSequence_nonneg z n) (Nat.cast_nonneg n)

/-- The directional mean constant is the Fekete limit of mean passage times
along a lattice ray, with the infimum taken over positive indices. -/
noncomputable def directionalMeanConstant
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) : ℝ :=
  (h.meanPassageSequence_isSubadditive hs hr z).lim

/-- Convergence in the native filter ℕ.atTop, including the zero direction. -/
theorem GammaEnvironment.meanPassageSequence_tendsto
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) :
    Tendsto (fun n : ℕ => meanPassageSequence P τ z n / (n : ℝ))
      atTop (𝓝 (directionalMeanConstant h hs hr z)) :=
  (h.meanPassageSequence_isSubadditive hs hr z).tendsto_lim
    (h.normalized_meanPassage_bddBelow z)

theorem GammaEnvironment.directionalMeanConstant_nonneg
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) : 0 ≤ directionalMeanConstant h hs hr z :=
  ge_of_tendsto (h.meanPassageSequence_tendsto hs hr z)
    (Filter.Eventually.of_forall fun n =>
      div_nonneg (h.meanPassageSequence_nonneg z n) (Nat.cast_nonneg n))

/-- Every positive-index finite mean bounds the limit above. The restriction
n≠0 is native to Fekete's infimum and is not discarded at total division zero. -/
theorem GammaEnvironment.directionalMeanConstant_le_normalized_mean
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) {n : ℕ} (hn : n ≠ 0) :
    directionalMeanConstant h hs hr z ≤ meanPassageSequence P τ z n / (n : ℝ) :=
  (h.meanPassageSequence_isSubadditive hs hr z).lim_le_div
    (h.normalized_meanPassage_bddBelow z) hn

theorem GammaEnvironment.directionalMeanConstant_le_mean
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) :
    directionalMeanConstant h hs hr z ≤
      ∫ ω, passageTime (fun e => τ e ω) 0 z ∂P := by
  have hb := h.directionalMeanConstant_le_normalized_mean hs hr z
    (n := 1) (by simp)
  simpa only [meanPassageSequence, one_nsmul, Nat.cast_one, div_one] using hb

/-- Deterministic path bound; every repeated traversal is charged. This is
finite but does not assert strict positivity in any nonzero direction. -/
theorem GammaEnvironment.directionalMeanConstant_le_path_length
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) (ds : List Step) (hend : (0 : Vertex) + displacement ds = z) :
    directionalMeanConstant h hs hr z ≤ (ds.length : ℝ) * (shape / rate) :=
  (h.directionalMeanConstant_le_mean hs hr z).trans
    (h.integral_passageTime_le_path_length hs hr 0 z ds hend)

/-- The zero direction is handled by the actual empty path, not a positivity
assumption or an exception to the convergence statement. -/
theorem GammaEnvironment.directionalMeanConstant_zero
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    directionalMeanConstant h hs hr (0 : Vertex) = 0 := by
  apply le_antisymm _ (h.directionalMeanConstant_nonneg hs hr 0)
  have hb := h.directionalMeanConstant_le_path_length hs hr 0 [] (by simp)
  simpa only [List.length_nil, Nat.cast_zero, zero_mul] using hb

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MeanAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory Filter Topology PlanarFPP

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Undirected reversal followed by translation, on the actual passage times. -/
theorem GammaEnvironment.integral_passageTime_neg
    (h : GammaEnvironment shape rate P τ) (z : Vertex) :
    (∫ ω, passageTime (fun e => τ e ω) 0 (-z) ∂P) =
      ∫ ω, passageTime (fun e => τ e ω) 0 z ∂P := by
  have hr : (∫ ω, passageTime (fun e => τ e ω) 0 (-z) ∂P) =
      ∫ ω, passageTime (fun e => τ e ω) (-z) 0 ∂P := by
    apply integral_congr_ae
    filter_upwards [h.ae_positive] with ω hω
    exact passageTime_symm _ (fun e => (hω e).le) 0 (-z)
  have ht := h.integral_passageTime_translate (-z) 0 z
  simp only [add_zero, neg_add_cancel] at ht
  exact hr.trans ht

theorem GammaEnvironment.meanPassageSequence_neg
    (h : GammaEnvironment shape rate P τ) (z : Vertex) (n : ℕ) :
    meanPassageSequence P τ (-z) n = meanPassageSequence P τ z n := by
  simpa only [meanPassageSequence, smul_neg] using
    h.integral_passageTime_neg (n • z)

theorem GammaEnvironment.directionalMeanConstant_neg
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) :
    directionalMeanConstant h hs hr (-z) = directionalMeanConstant h hs hr z := by
  have hn := h.meanPassageSequence_tendsto hs hr (-z)
  simp only [h.meanPassageSequence_neg] at hn
  exact tendsto_nhds_unique hn (h.meanPassageSequence_tendsto hs hr z)

/-- Limit order applied to finite, integrable mean subadditivity. -/
theorem GammaEnvironment.directionalMeanConstant_add_le
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (x y : Vertex) :
    directionalMeanConstant h hs hr (x + y) ≤
      directionalMeanConstant h hs hr x + directionalMeanConstant h hs hr y := by
  apply le_of_tendsto_of_tendsto (h.meanPassageSequence_tendsto hs hr (x + y))
    ((h.meanPassageSequence_tendsto hs hr x).add
      (h.meanPassageSequence_tendsto hs hr y))
  apply Filter.Eventually.of_forall
  intro n
  have hb := h.mean_passageTime_subadditive hs hr (n • x) (n • y)
  have hd := div_le_div_of_nonneg_right hb (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa only [meanPassageSequence, smul_add, add_div] using hd

/-- Cofinality of positive natural multiples, proved without a real-index limit. -/
theorem tendsto_nat_right_multiple (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n : ℕ => n * k) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro b
  refine ⟨b, ?_⟩
  intro n hn
  exact hn.trans (by simpa only [Nat.succ_eq_add_one, zero_add, mul_one] using
    Nat.mul_le_mul_left n (Nat.succ_le_iff.mpr hk))

/-- Natural homogeneity follows from the cofinal subsequence n*k, not an
assumed homogeneous extension. The zero multiplier is a separate case. -/
theorem GammaEnvironment.directionalMeanConstant_nsmul
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) (k : ℕ) :
    directionalMeanConstant h hs hr (k • z) =
      (k : ℝ) * directionalMeanConstant h hs hr z := by
  by_cases hk : k = 0
  · subst k
    simpa only [zero_smul, Nat.cast_zero, zero_mul] using
      h.directionalMeanConstant_zero hs hr
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have ht := ((h.meanPassageSequence_tendsto hs hr z).comp
    (tendsto_nat_right_multiple k (Nat.pos_of_ne_zero hk))).const_mul (k : ℝ)
  have he : (fun n : ℕ => (k : ℝ) *
      (meanPassageSequence P τ z (n * k) / ((n * k : ℕ) : ℝ))) =
      (fun n : ℕ => meanPassageSequence P τ (k • z) n / (n : ℝ)) := by
    funext n
    have hsml : meanPassageSequence P τ z (n * k) =
        meanPassageSequence P τ (k • z) n := by
      simp only [meanPassageSequence, mul_smul]
    rw [hsml, Nat.cast_mul, ← mul_div_assoc,
      mul_comm (k : ℝ) (meanPassageSequence P τ (k • z) n),
      mul_div_mul_right _ _ hkR]
  change Tendsto (fun n : ℕ => (k : ℝ) *
    (meanPassageSequence P τ z (n * k) / ((n * k : ℕ) : ℝ)))
    atTop (𝓝 ((k : ℝ) * directionalMeanConstant h hs hr z)) at ht
  rw [he] at ht
  exact tendsto_nhds_unique (h.meanPassageSequence_tendsto hs hr (k • z)) ht

/-- Integer homogeneity, with |k| represented by its exact natural absolute
value. This includes k=0, negative multipliers, and the zero direction. -/
theorem GammaEnvironment.directionalMeanConstant_zsmul
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) (k : ℤ) :
    directionalMeanConstant h hs hr (k • z) =
      (k.natAbs : ℝ) * directionalMeanConstant h hs hr z := by
  cases k with
  | ofNat n =>
      simpa only [Int.ofNat_eq_natCast, natCast_zsmul, Int.natAbs_natCast] using
        h.directionalMeanConstant_nsmul hs hr z n
  | negSucc n =>
      change directionalMeanConstant h hs hr (Int.negSucc n • z) =
        ((n + 1 : ℕ) : ℝ) * directionalMeanConstant h hs hr z
      rw [negSucc_zsmul, h.directionalMeanConstant_neg hs hr]
      exact h.directionalMeanConstant_nsmul hs hr z (n + 1)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MeanLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory PlanarFPP

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- The horizontal-then-vertical coordinate path has exactly the lattice `L¹` length. -/
theorem coordinate_path_length_l1 (p q : Vertex) :
    (coordinatePath p q).length = latticeDistance p q := by
  have hh (a : ℤ) : (horizontal a).length = a.natAbs := by
    unfold horizontal
    split_ifs <;> simp only [List.length_replicate] <;> omega
  have hv (a : ℤ) : (vertical a).length = a.natAbs := by
    unfold vertical
    split_ifs <;> simp only [List.length_replicate] <;> omega
  simp [coordinatePath, latticeDistance, hh, hv]

/-- The finite first-moment path bound controls the actual Fekete constant. -/
theorem GammaEnvironment.directionalMeanConstant_le_l1
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) :
    directionalMeanConstant h hs hr z ≤
      (shape / rate) * ((z.1.natAbs + z.2.natAbs : ℕ) : ℝ) := by
  have hb := h.directionalMeanConstant_le_path_length hs hr z
    (coordinatePath 0 z) (coordinatePath_endpoint 0 z)
  rw [coordinate_path_length_l1] at hb
  simpa [latticeDistance, mul_comm] using hb

/-- Reverse triangle inequality for the actual lattice mean constants. -/
theorem GammaEnvironment.abs_directionalMeanConstant_sub_le
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (x y : Vertex) :
    |directionalMeanConstant h hs hr x - directionalMeanConstant h hs hr y| ≤
      directionalMeanConstant h hs hr (x - y) := by
  have hx := h.directionalMeanConstant_add_le hs hr (x-y) y
  rw [sub_add_cancel] at hx
  have hy := h.directionalMeanConstant_add_le hs hr (y-x) x
  rw [sub_add_cancel] at hy
  have he : directionalMeanConstant h hs hr (y-x) =
      directionalMeanConstant h hs hr (x-y) := by
    rw [show y-x = -(x-y) by exact (neg_sub x y).symm,
      h.directionalMeanConstant_neg hs hr]
  rw [he] at hy
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- L1-Lipschitz estimate, with the true Gamma mean shape/rate, all lattice
vertices, and no time-norm, positivity-of-limit or almost-sure premise. -/
theorem GammaEnvironment.directionalMeanConstant_l1_lipschitz
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (x y : Vertex) :
    |directionalMeanConstant h hs hr x - directionalMeanConstant h hs hr y| ≤
      (shape / rate) * (((x.1-y.1).natAbs + (x.2-y.2).natAbs : ℕ) : ℝ) := by
  exact (h.abs_directionalMeanConstant_sub_le hs hr x y).trans
    (h.directionalMeanConstant_le_l1 hs hr (x-y))

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_RationalMean
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open PlanarFPP

/-- A rational pair represented by one positive natural denominator. -/
def rationalLatticePoint (x : Vertex) (n : ℕ) : ℚ × ℚ :=
  ((x.1 : ℚ) / (n : ℚ), (x.2 : ℚ) / (n : ℚ))

def rationalDenominator (q : ℚ × ℚ) : ℕ := q.1.den * q.2.den

def rationalNumerator (q : ℚ × ℚ) : Vertex :=
  (q.1.num * (q.2.den : ℤ), q.2.num * (q.1.den : ℤ))

theorem rationalDenominator_pos (q : ℚ × ℚ) : 0 < rationalDenominator q :=
  Nat.mul_pos q.1.den_pos q.2.den_pos

/-- Explicit common-denominator representation, including zero coordinates. -/
theorem rationalLatticePoint_numerator_denominator (q : ℚ × ℚ) :
    rationalLatticePoint (rationalNumerator q) (rationalDenominator q) = q := by
  have h₁ : (q.1.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.1.den_ne_zero
  have h₂ : (q.2.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.2.den_ne_zero
  apply Prod.ext
  · change ((q.1.num * (q.2.den : ℤ) : ℤ) : ℚ) /
      ((q.1.den * q.2.den : ℕ) : ℚ) = q.1
    rw [Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    calc
      _ = (q.1.num : ℚ) / (q.1.den : ℚ) := by field_simp
      _ = q.1 := q.1.num_div_den
  · change ((q.2.num * (q.1.den : ℤ) : ℤ) : ℚ) /
      ((q.1.den * q.2.den : ℕ) : ℚ) = q.2
    rw [Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    calc
      _ = (q.2.num : ℚ) / (q.2.den : ℚ) := by field_simp
      _ = q.2 := q.2.num_div_den

/-- Equality of rational points yields equality after integer cross multiplication. -/
theorem rationalLatticePoint_cross {x y : Vertex} {n k : ℕ}
    (hn : 0 < n) (hk : 0 < k)
    (he : rationalLatticePoint x n = rationalLatticePoint y k) :
    k • x = n • y := by
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hkQ : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  have hx := (div_eq_div_iff hnQ hkQ).mp (congrArg Prod.fst he)
  have hy := (div_eq_div_iff hnQ hkQ).mp (congrArg Prod.snd he)
  have hxZ : x.1 * (k : ℤ) = y.1 * (n : ℤ) := by exact_mod_cast hx
  have hyZ : x.2 * (k : ℤ) = y.2 * (n : ℤ) := by exact_mod_cast hy
  apply Prod.ext
  · change k • x.1 = n • y.1
    simpa only [nsmul_eq_mul, mul_comm] using hxZ
  · change k • x.2 = n • y.2
    simpa only [nsmul_eq_mul, mul_comm] using hyZ

/-- Denominator compatibility derived from homogeneity, not assumed as a premise. -/
theorem latticeMean_div_eq_of_cross (m : Vertex → ℝ)
    (hm : ∀ (k : ℕ) (x : Vertex), m (k • x) = (k : ℝ) * m x)
    {x y : Vertex} {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (he : k • x = n • y) : m x / (n : ℝ) = m y / (k : ℝ) := by
  have h := congrArg m he
  rw [hm, hm] at h
  apply (div_eq_div_iff (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk))).mpr
  simpa only [mul_comm] using h

/-- A concrete rational mean; no representative is chosen nonconstructively. -/
noncomputable def rationalMean (m : Vertex → ℝ) (q : ℚ × ℚ) : ℝ :=
  m (rationalNumerator q) / (rationalDenominator q : ℝ)

/-- Evaluation at every integer pair over every positive natural denominator. -/
theorem rationalMean_rationalLatticePoint (m : Vertex → ℝ)
    (hm : ∀ (k : ℕ) (x : Vertex), m (k • x) = (k : ℝ) * m x)
    (x : Vertex) (n : ℕ) (hn : 0 < n) :
    rationalMean m (rationalLatticePoint x n) = m x / (n : ℝ) := by
  let q := rationalLatticePoint x n
  have he : rationalLatticePoint (rationalNumerator q) (rationalDenominator q) =
      rationalLatticePoint x n := rationalLatticePoint_numerator_denominator q
  exact latticeMean_div_eq_of_cross m hm (rationalDenominator_pos q) hn
    (rationalLatticePoint_cross (rationalDenominator_pos q) hn he)

/-- Literal agreement with the integer lattice (denominator one). -/
theorem rationalMean_integerPair (m : Vertex → ℝ)
    (hm : ∀ (k : ℕ) (x : Vertex), m (k • x) = (k : ℝ) * m x)
    (x : Vertex) : rationalMean m ((x.1 : ℚ), (x.2 : ℚ)) = m x := by
  simpa [rationalLatticePoint] using rationalMean_rationalLatticePoint m hm x 1 (by decide)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_RationalMeanAlgebra
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open PlanarFPP

lemma rationalLatticePoint_scale (x : Vertex) (n k : ℕ) (hk : 0 < k) :
    rationalLatticePoint (k • x) (k*n) = rationalLatticePoint x n := by
  have hkQ : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  apply Prod.ext <;> simp [rationalLatticePoint, mul_div_mul_left, hkQ]

lemma rationalLatticePoint_add (x y : Vertex) (n : ℕ) :
    rationalLatticePoint (x+y) n = rationalLatticePoint x n + rationalLatticePoint y n := by
  ext <;> simp [rationalLatticePoint, add_div]

lemma rationalLatticePoint_neg (x : Vertex) (n : ℕ) :
    rationalLatticePoint (-x) n = -rationalLatticePoint x n := by
  ext <;> simp [rationalLatticePoint, neg_div]

/-- Simultaneous positive common denominator, without canonical-denominator
identities for addition or subtraction. -/
lemma rationalPair_common_denominator (q r : ℚ × ℚ) :
    ∃ n : ℕ, 0 < n ∧ ∃ x y : Vertex,
      q = rationalLatticePoint x n ∧ r = rationalLatticePoint y n := by
  let d := rationalDenominator q
  let e := rationalDenominator r
  refine ⟨e*d, Nat.mul_pos (rationalDenominator_pos r) (rationalDenominator_pos q),
    e • rationalNumerator q, d • rationalNumerator r, ?_, ?_⟩
  · rw [rationalLatticePoint_scale _ _ _ (rationalDenominator_pos r)]
    exact (rationalLatticePoint_numerator_denominator q).symm
  · rw [show e*d = d*e by exact Nat.mul_comm e d,
      rationalLatticePoint_scale _ _ _ (rationalDenominator_pos q)]
    exact (rationalLatticePoint_numerator_denominator r).symm

lemma rationalMean_zero (m : Vertex → ℝ)
    (hn : ∀ (k : ℕ) (x : Vertex), m (k • x) = (k : ℝ)*m x)
    (hzero : m 0 = 0) : rationalMean m 0 = 0 := by
  change rationalMean m (0, 0) = 0
  simpa [hzero] using rationalMean_integerPair m hn 0

lemma rationalMean_add_le (m : Vertex → ℝ)
    (hn : ∀ (k : ℕ) (x : Vertex), m (k • x) = (k : ℝ)*m x)
    (hadd : ∀ x y, m (x+y) ≤ m x+m y) (q r : ℚ × ℚ) :
    rationalMean m (q+r) ≤ rationalMean m q+rationalMean m r := by
  obtain ⟨n, hp, x, y, rfl, rfl⟩ := rationalPair_common_denominator q r
  rw [← rationalLatticePoint_add, rationalMean_rationalLatticePoint m hn _ _ hp,
    rationalMean_rationalLatticePoint m hn _ _ hp,
    rationalMean_rationalLatticePoint m hn _ _ hp, ← add_div]
  exact div_le_div_of_nonneg_right (hadd x y) (Nat.cast_nonneg n)

lemma rationalMean_neg (m : Vertex → ℝ)
    (hn : ∀ (k : ℕ) (x : Vertex), m (k • x) = (k : ℝ)*m x)
    (hneg : ∀ x, m (-x) = m x) (q : ℚ × ℚ) :
    rationalMean m (-q) = rationalMean m q := by
  have he := rationalLatticePoint_numerator_denominator q
  conv_lhs => rw [← he, ← rationalLatticePoint_neg]
  rw [rationalMean_rationalLatticePoint m hn _ _ (rationalDenominator_pos q), hneg]
  rfl

lemma rationalLatticePoint_rat_smul (a : ℚ) (x : Vertex) (n : ℕ) :
    rationalLatticePoint (a.num • x) (a.den*n) = a • rationalLatticePoint x n := by
  apply Prod.ext
  · change ((a.num • x.1 : ℤ) : ℚ)/((a.den*n : ℕ) : ℚ) =
      a*((x.1 : ℚ)/(n : ℚ))
    rw [zsmul_eq_mul, Int.cast_id, Int.cast_mul, Nat.cast_mul]
    calc
      _ = ((a.num : ℚ)/(a.den : ℚ))*((x.1 : ℚ)/(n : ℚ)) := by ring
      _ = _ := by rw [a.num_div_den]
  · change ((a.num • x.2 : ℤ) : ℚ)/((a.den*n : ℕ) : ℚ) =
      a*((x.2 : ℚ)/(n : ℚ))
    rw [zsmul_eq_mul, Int.cast_id, Int.cast_mul, Nat.cast_mul]
    calc
      _ = ((a.num : ℚ)/(a.den : ℚ))*((x.2 : ℚ)/(n : ℚ)) := by ring
      _ = _ := by rw [a.num_div_den]

/-- Signed rational scalars include zero; positivity is needed only for the
canonical denominator, never for the numerator. -/
lemma rationalMean_smul (m : Vertex → ℝ)
    (hn : ∀ (k : ℕ) (x : Vertex), m (k • x) = (k : ℝ)*m x)
    (hz : ∀ (k : ℤ) (x : Vertex), m (k • x) = (k.natAbs : ℝ)*m x)
    (a : ℚ) (q : ℚ × ℚ) :
    rationalMean m (a • q) = |(a : ℝ)| * rationalMean m q := by
  let d := rationalDenominator q
  let x := rationalNumerator q
  have hd : 0 < d := rationalDenominator_pos q
  have he : rationalLatticePoint x d = q := rationalLatticePoint_numerator_denominator q
  rw [← he, ← rationalLatticePoint_rat_smul,
    rationalMean_rationalLatticePoint m hn _ _ (Nat.mul_pos a.den_pos hd),
    rationalMean_rationalLatticePoint m hn _ _ hd, hz, Nat.cast_mul]
  have ha : |(a : ℝ)| = (a.num.natAbs : ℝ)/(a.den : ℝ) := by
    rw [Rat.cast_def, abs_div, abs_of_pos (show (0 : ℝ) < (a.den : ℝ) from Nat.cast_pos.mpr a.den_pos), Nat.cast_natAbs, Int.cast_abs]
  rw [ha]
  ring

/-- Exact L1 distance for a positive common denominator. -/
lemma rationalLatticePoint_real_l1 (x y : Vertex) (n : ℕ) (hn : 0 < n) :
    |((rationalLatticePoint x n).1 : ℝ)-((rationalLatticePoint y n).1 : ℝ)| +
      |((rationalLatticePoint x n).2 : ℝ)-((rationalLatticePoint y n).2 : ℝ)| =
      (((x.1-y.1).natAbs+(x.2-y.2).natAbs : ℕ) : ℝ)/(n : ℝ) := by
  simp only [rationalLatticePoint, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast,
    ← sub_div, abs_div, abs_of_pos (show (0 : ℝ) < (n : ℝ) from Nat.cast_pos.mpr hn), Nat.cast_add,
    Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, add_div]

lemma rationalMean_l1 (m : Vertex → ℝ)
    (hn : ∀ (k : ℕ) (x : Vertex), m (k • x) = (k : ℝ)*m x)
    (C : ℝ)
    (hl : ∀ x y, |m x-m y| ≤ C *
      (((x.1-y.1).natAbs+(x.2-y.2).natAbs : ℕ) : ℝ))
    (q r : ℚ × ℚ) :
    |rationalMean m q-rationalMean m r| ≤ C *
      (|(q.1 : ℝ)-(r.1 : ℝ)|+|(q.2 : ℝ)-(r.2 : ℝ)|) := by
  obtain ⟨n, hp, x, y, rfl, rfl⟩ := rationalPair_common_denominator q r
  rw [rationalMean_rationalLatticePoint m hn _ _ hp,
    rationalMean_rationalLatticePoint m hn _ _ hp, ← sub_div, abs_div,
    abs_of_pos (show (0 : ℝ) < (n : ℝ) from Nat.cast_pos.mpr hp), rationalLatticePoint_real_l1 x y n hp]
  have hb := div_le_div_of_nonneg_right (hl x y) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa only [mul_div_assoc] using hb

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_RealMeanExtension
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open Topology
open scoped NNReal

/-- The rational embedding uses the standard product (maximum) metric. -/
def rationalPairCast (q : ℚ × ℚ) : ℝ × ℝ := ((q.1 : ℝ), (q.2 : ℝ))

lemma rationalPairCast_uniformEmbedding : IsUniformEmbedding rationalPairCast :=
  Rat.isUniformEmbedding_coe_real.prod Rat.isUniformEmbedding_coe_real

lemma rationalPairCast_dense : DenseRange rationalPairCast :=
  Rat.isDenseEmbedding_coe_real.dense.prodMap Rat.isDenseEmbedding_coe_real.dense

@[simp] lemma rationalPairCast_add (q r : ℚ × ℚ) :
    rationalPairCast (q+r) = rationalPairCast q + rationalPairCast r := by
  ext <;> simp [rationalPairCast]

@[simp] lemma rationalPairCast_neg (q : ℚ × ℚ) :
    rationalPairCast (-q) = -rationalPairCast q := by
  ext <;> simp [rationalPairCast]

@[simp] lemma rationalPairCast_smul (a : ℚ) (q : ℚ × ℚ) :
    rationalPairCast (a • q) = (a : ℝ) • rationalPairCast q := by
  ext <;> simp [rationalPairCast, smul_eq_mul]

/-- L1 is at most twice the standard product maximum metric. -/
lemma rational_l1_lipschitz (f : ℚ × ℚ → ℝ) (C : ℝ≥0)
    (h : ∀ q r, |f q-f r| ≤ (C : ℝ) *
      (|(q.1 : ℝ)-(r.1 : ℝ)| + |(q.2 : ℝ)-(r.2 : ℝ)|)) :
    LipschitzWith (2*C) f := by
  apply LipschitzWith.of_dist_le_mul
  intro q r
  rw [Real.dist_eq, Prod.dist_eq, Rat.dist_eq, Rat.dist_eq]
  have h₁ := le_max_left |(q.1 : ℝ)-(r.1 : ℝ)| |(q.2 : ℝ)-(r.2 : ℝ)|
  have h₂ := le_max_right |(q.1 : ℝ)-(r.1 : ℝ)| |(q.2 : ℝ)-(r.2 : ℝ)|
  have hh := mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) C.coe_nonneg
  have hb := h q r
  simp only [NNReal.coe_mul, NNReal.coe_ofNat]
  nlinarith

noncomputable def realMeanExtension (f : ℚ × ℚ → ℝ) : ℝ × ℝ → ℝ :=
  (rationalPairCast_uniformEmbedding.isUniformInducing.isDenseInducing
    rationalPairCast_dense).extend f

lemma realMeanExtension_uniformContinuous {f : ℚ × ℚ → ℝ}
    (hf : UniformContinuous f) : UniformContinuous (realMeanExtension f) :=
  uniformContinuous_uniformly_extend
    rationalPairCast_uniformEmbedding.isUniformInducing rationalPairCast_dense hf

lemma realMeanExtension_on_rat {f : ℚ × ℚ → ℝ}
    (hf : UniformContinuous f) (q : ℚ × ℚ) :
    realMeanExtension f (rationalPairCast q) = f q :=
  (rationalPairCast_uniformEmbedding.isUniformInducing.isDenseInducing
    rationalPairCast_dense).extend_eq hf.continuous q

lemma realMeanExtension_add_le {f : ℚ × ℚ → ℝ} (hf : UniformContinuous f)
    (hadd : ∀ q r, f (q+r) ≤ f q + f r) (x y : ℝ × ℝ) :
    realMeanExtension f (x+y) ≤ realMeanExtension f x + realMeanExtension f y := by
  have hc := (realMeanExtension_uniformContinuous hf).continuous
  apply isClosed_property2 rationalPairCast_dense
    (p := fun x y => realMeanExtension f (x+y) ≤
      realMeanExtension f x + realMeanExtension f y) ?_ ?_ x y
  · exact isClosed_le (hc.comp (continuous_fst.add continuous_snd))
      ((hc.comp continuous_fst).add (hc.comp continuous_snd))
  · intro q r
    rw [← rationalPairCast_add, realMeanExtension_on_rat hf,
      realMeanExtension_on_rat hf, realMeanExtension_on_rat hf]
    exact hadd q r

lemma realMeanExtension_neg {f : ℚ × ℚ → ℝ} (hf : UniformContinuous f)
    (hneg : ∀ q, f (-q) = f q) (x : ℝ × ℝ) :
    realMeanExtension f (-x) = realMeanExtension f x := by
  have hc := (realMeanExtension_uniformContinuous hf).continuous
  apply isClosed_property rationalPairCast_dense
    (p := fun x => realMeanExtension f (-x) = realMeanExtension f x) ?_ ?_ x
  · exact isClosed_eq (hc.comp continuous_neg) hc
  · intro q
    rw [← rationalPairCast_neg, realMeanExtension_on_rat hf, realMeanExtension_on_rat hf]
    exact hneg q

/-- Density in the scalar AND vector proves full real homogeneity. -/
lemma realMeanExtension_smul {f : ℚ × ℚ → ℝ} (hf : UniformContinuous f)
    (hsmul : ∀ (a : ℚ) q, f (a • q) = |(a : ℝ)| * f q)
    (a : ℝ) (x : ℝ × ℝ) :
    realMeanExtension f (a • x) = |a| * realMeanExtension f x := by
  have hc := (realMeanExtension_uniformContinuous hf).continuous
  have hd := Rat.isDenseEmbedding_coe_real.dense.prodMap rationalPairCast_dense
  apply isClosed_property hd
    (p := fun z : ℝ × (ℝ × ℝ) => realMeanExtension f (z.1 • z.2) =
      |z.1| * realMeanExtension f z.2) ?_ ?_ (a,x)
  · exact isClosed_eq (hc.comp (continuous_fst.smul continuous_snd))
      (continuous_fst.abs.mul (hc.comp continuous_snd))
  · intro z
    change realMeanExtension f ((z.1 : ℝ) • rationalPairCast z.2) =
      |(z.1 : ℝ)| * realMeanExtension f (rationalPairCast z.2)
    rw [← rationalPairCast_smul, realMeanExtension_on_rat hf, realMeanExtension_on_rat hf]
    exact hsmul z.1 z.2

/-- Construct, rather than assume, a real seminorm from rational data. -/
noncomputable def realMeanSeminorm (f : ℚ × ℚ → ℝ) (C : ℝ≥0)
    (hlip : ∀ q r, |f q-f r| ≤ (C : ℝ) *
      (|(q.1 : ℝ)-(r.1 : ℝ)| + |(q.2 : ℝ)-(r.2 : ℝ)|))
    (hzero : f 0 = 0) (hadd : ∀ q r, f (q+r) ≤ f q + f r)
    (hneg : ∀ q, f (-q) = f q)
    (hsmul : ∀ (a : ℚ) q, f (a • q) = |(a : ℝ)| * f q) :
    Seminorm ℝ (ℝ × ℝ) where
  toFun := realMeanExtension f
  map_zero' := by
    change realMeanExtension f (0, 0) = 0
    have h := realMeanExtension_on_rat (rational_l1_lipschitz f C hlip).uniformContinuous 0
    simpa [rationalPairCast, hzero] using h
  add_le' := realMeanExtension_add_le (rational_l1_lipschitz f C hlip).uniformContinuous hadd
  neg' := realMeanExtension_neg (rational_l1_lipschitz f C hlip).uniformContinuous hneg
  smul' := by
    intro a x
    simpa only [Real.norm_eq_abs] using
      realMeanExtension_smul (rational_l1_lipschitz f C hlip).uniformContinuous hsmul a x

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MeanPairSeminorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory PlanarFPP

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

noncomputable def gammaMeanPairSeminorm
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    Seminorm ℝ (ℝ × ℝ) := by
  let m : Vertex → ℝ := directionalMeanConstant h hs hr
  have hn : ∀ (k : ℕ) (x : Vertex), m (k • x) = (k : ℝ)*m x :=
    fun k x => h.directionalMeanConstant_nsmul hs hr x k
  have hz : ∀ (k : ℤ) (x : Vertex), m (k • x) = (k.natAbs : ℝ)*m x :=
    fun k x => h.directionalMeanConstant_zsmul hs hr x k
  exact realMeanSeminorm (rationalMean m) ⟨shape/rate, (div_pos hs hr).le⟩
    (rationalMean_l1 m hn (shape/rate) (h.directionalMeanConstant_l1_lipschitz hs hr))
    (rationalMean_zero m hn (h.directionalMeanConstant_zero hs hr))
    (rationalMean_add_le m hn (h.directionalMeanConstant_add_le hs hr))
    (rationalMean_neg m hn (h.directionalMeanConstant_neg hs hr))
    (rationalMean_smul m hn hz)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_FiniteMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ν : Measure ℝ} {P : Measure Ω} {τ : PlanarFPP.Edge → Ω → ℝ}

/-- The cost of a deterministic finite set of distinct undirected edges. -/
def edgeSum (S : Finset PlanarFPP.Edge) (τ : PlanarFPP.Edge → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ e ∈ S, τ e ω

omit [MeasurableSpace Ω] in
@[simp] lemma edgeSum_empty (τ : PlanarFPP.Edge → Ω → ℝ) (ω : Ω) :
    edgeSum ∅ τ ω = 0 := by simp [edgeSum]

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CheapPathCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Finset
open scoped ENNReal

/-- There are four possible nearest-neighbor steps on the square lattice. -/
local instance cheapStepFintype : Fintype Step where
  elems := {Step.east, Step.west, Step.north, Step.south}
  complete d := by cases d <;> simp

/-- Includes every actual step list of length n, without a simplicity restriction. -/
noncomputable def fixedStepLists (n : ℕ) : Finset (List Step) :=
  Finset.univ.image (fun f : Fin n → Step => List.ofFn f)

lemma mem_fixedStepLists (n : ℕ) (ds : List Step) :
    ds ∈ fixedStepLists n ↔ ds.length = n := by
  classical
  constructor
  · intro h
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp h
    exact List.length_ofFn
  · intro h
    subst n
    apply Finset.mem_image.mpr
    exact ⟨ds.get, Finset.mem_univ _, List.ofFn_get ds⟩

/-- The probability bound uses only the subfamily with distinct undirected edges. -/
noncomputable def fixedTrailLists (p : Vertex) (n : ℕ) : Finset (List Step) := by
  classical
  exact (fixedStepLists n).filter (fun ds => ((trace p ds).map traversalEdge).Nodup)

lemma mem_fixedTrailLists (p : Vertex) (n : ℕ) (ds : List Step) :
    ds ∈ fixedTrailLists p n ↔
      ds.length = n ∧ ((trace p ds).map traversalEdge).Nodup := by
  classical
  simp only [fixedTrailLists, Finset.mem_filter, mem_fixedStepLists]

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CheapPathDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP
open scoped ENNReal

noncomputable def cheapChernoff (shape rate : ℝ) : ℝ :=
  rate * (Real.exp (Real.log 16 / shape) - 1)

noncomputable def cheapSlope (shape rate : ℝ) : ℝ :=
  Real.log 2 / cheapChernoff shape rate

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CheapLongTrails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Cheap trails at one exact length and one deterministic starting vertex. -/
def cheapTrailEvent (shape rate : ℝ) (τ : Edge → Ω → ℝ)
    (p : Vertex) (n : ℕ) : Set Ω :=
  {ω | ∃ ds : List Step, ds.length = n ∧
    ((trace p ds).map traversalEdge).Nodup ∧
      pathCost (fun e => τ e ω) p ds ≤ cheapSlope shape rate * (n : ℝ)}

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_LoopErasure
attribute [-instance] _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.LoopGraph
variable {V : Type*} {G : SimpleGraph V}

/-- Undirected edge weights; the domain contains only actual edges. -/
abbrev Weights (G : SimpleGraph V) := G.edgeSet → ℝ

def edgeCost (w : Weights G) {x y : V} (h : G.Adj x y) : ℝ :=
  w ⟨s(x, y), h⟩

@[simp] theorem edgeCost_symm (w : Weights G) {x y : V} (h : G.Adj x y) :
    edgeCost w h.symm = edgeCost w h := by
  simp only [edgeCost, Sym2.eq_swap]

/-- Recursion counts repeated traversals with multiplicity. -/
def pathCost (w : Weights G) {x y : V} : G.Walk x y → ℝ
  | .nil => 0
  | .cons h p => edgeCost w h + pathCost w p

@[simp] theorem pathCost_nil (w : Weights G) (x : V) :
    pathCost w (SimpleGraph.Walk.nil : G.Walk x x) = 0 := rfl

@[simp] theorem pathCost_cons (w : Weights G) {x y z : V}
    (h : G.Adj x y) (p : G.Walk y z) :
    pathCost w (.cons h p) = edgeCost w h + pathCost w p := rfl

lemma pathCost_eq_darts_sum (w : Weights G) {x y : V} (p : G.Walk x y) :
    pathCost w p = (p.darts.map (fun d => edgeCost w d.adj)).sum := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [ih, edgeCost]

/-- Loop erasure does not increase a path's physical cost. -/
theorem bypass_cost_le [DecidableEq V] (w : Weights G) (hw : ∀ e, 0 ≤ w e)
    {x y : V} (p : G.Walk x y) : pathCost w p.bypass ≤ pathCost w p := by
  rw [pathCost_eq_darts_sum, pathCost_eq_darts_sum]
  apply (p.darts_bypass_sublist_darts.map (fun d => edgeCost w d.adj)).sum_le_sum
  intro a ha
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp ha
  exact hw _

abbrev Vertex := ℤ × ℤ

def lattice : SimpleGraph Vertex where
  Adj x y := |x.1 - y.1| + |x.2 - y.2| = 1
  symm := ⟨by intros x y h; simpa only [abs_sub_comm] using h⟩
  loopless := ⟨by intro x; simp⟩

abbrev Edge := lattice.edgeSet
abbrev Environment := Weights lattice

end GammaFPP.LoopGraph

namespace GammaFPP.LoopErase
open PlanarFPP

lemma companion_adj_step (p : Vertex) (d : Step) :
    GammaFPP.LoopGraph.lattice.Adj p (p+d.delta) := by
  cases d <;> simp [GammaFPP.LoopGraph.lattice, Step.delta]

lemma companion_adj_iff (p q : Vertex) :
    GammaFPP.LoopGraph.lattice.Adj p q ↔ ∃ d : Step, q=p+d.delta := by
  constructor
  · intro h
    change |p.1-q.1|+|p.2-q.2|=1 at h
    have hor : (q.1=p.1+1 ∧ q.2=p.2) ∨ (q.1=p.1-1 ∧ q.2=p.2) ∨
        (q.1=p.1 ∧ q.2=p.2+1) ∨ (q.1=p.1 ∧ q.2=p.2-1) := by
      simp only [abs_eq_max_neg] at h
      omega
    rcases hor with h | h | h | h
    · exact ⟨.east, by ext <;> simp_all [Step.delta,sub_eq_add_neg]⟩
    · exact ⟨.west, by ext <;> simp_all [Step.delta,sub_eq_add_neg]⟩
    · exact ⟨.north, by ext <;> simp_all [Step.delta,sub_eq_add_neg]⟩
    · exact ⟨.south, by ext <;> simp_all [Step.delta,sub_eq_add_neg]⟩
  · rintro ⟨d,rfl⟩
    exact companion_adj_step p d

def companionEdge (e : Edge) : GammaFPP.LoopGraph.Edge :=
  if e.2 = true then ⟨s(e.1,e.1+Step.north.delta), companion_adj_step _ _⟩
  else ⟨s(e.1,e.1+Step.east.delta), companion_adj_step _ _⟩

lemma companionEdge_step (p : Vertex) (d : Step) :
    companionEdge (d.edge p) = ⟨s(p,p+d.delta),companion_adj_step p d⟩ := by
  apply Subtype.ext
  cases d <;> simp [companionEdge,Step.edge,Step.delta,Prod.ext_iff]

lemma companionEdge_injective : Function.Injective companionEdge := by
  rintro ⟨⟨px,py⟩,b⟩ ⟨⟨qx,qy⟩,c⟩ h
  have he := congrArg Subtype.val h
  cases b <;> cases c <;>
    simp [companionEdge,Step.delta,Prod.ext_iff] at he ⊢ <;>
    rcases he with h | h <;> omega

lemma companionEdge_surjective : Function.Surjective companionEdge := by
  rintro ⟨e,he⟩
  induction e using Sym2.inductionOn with
  | hf p q =>
    obtain ⟨d,rfl⟩ := (companion_adj_iff p q).mp he
    exact ⟨d.edge p,companionEdge_step p d⟩

noncomputable def companionEdgeEquiv : Edge ≃ GammaFPP.LoopGraph.Edge :=
  Equiv.ofBijective companionEdge ⟨companionEdge_injective,companionEdge_surjective⟩

noncomputable def companionWeights (w : Edge → ℝ) : GammaFPP.LoopGraph.Environment :=
  fun e => w (companionEdgeEquiv.symm e)

@[simp] lemma companionWeights_edge (w : Edge → ℝ) (e : Edge) :
    companionWeights w (companionEdge e)=w e := by
  change w (companionEdgeEquiv.symm (companionEdgeEquiv e))=w e
  rw [companionEdgeEquiv.symm_apply_apply]

@[simp] lemma companion_pathCost_copy (w : GammaFPP.LoopGraph.Environment)
    {p q p' q' : Vertex} (walk : GammaFPP.LoopGraph.lattice.Walk p q) (hp : p=p') (hq : q=q') :
    GammaFPP.LoopGraph.pathCost w (walk.copy hp hq) = GammaFPP.LoopGraph.pathCost w walk := by
  subst p'; subst q'; rfl

lemma steps_companion_walk (w : Edge → ℝ) (p : Vertex) (ds : List Step) :
    ∃ walk : GammaFPP.LoopGraph.lattice.Walk p (p+displacement ds),
      GammaFPP.LoopGraph.pathCost (companionWeights w) walk = pathCost w p ds := by
  induction ds generalizing p with
  | nil =>
    refine ⟨(SimpleGraph.Walk.nil : GammaFPP.LoopGraph.lattice.Walk p p).copy rfl (by simp),?_⟩
    rw [companion_pathCost_copy]
    rfl
  | cons d ds ih =>
    obtain ⟨walk,hw⟩ := ih (p+d.delta)
    have he : (p+d.delta)+displacement ds = p+displacement (d::ds) := by
      simp [add_assoc]
    refine ⟨(SimpleGraph.Walk.cons (companion_adj_step p d) walk).copy rfl he,?_⟩
    simp only [companion_pathCost_copy, GammaFPP.LoopGraph.pathCost_cons, GammaFPP.LoopGraph.edgeCost, pathCost, hw]
    rw [← companionEdge_step,companionWeights_edge]

/-- The walk-to-step bridge preserves the ordered list of unoriented edges,
in addition to endpoints and traversal-counted cost. -/
lemma companion_walk_steps_edges (w : Edge → ℝ) {p q : Vertex}
    (walk : GammaFPP.LoopGraph.lattice.Walk p q) :
    ∃ ds : List Step, p+displacement ds=q ∧
      pathCost w p ds=GammaFPP.LoopGraph.pathCost (companionWeights w) walk ∧
      ((trace p ds).map (fun t => (companionEdge (traversalEdge t)).val))=walk.edges := by
  induction walk with
  | nil => exact ⟨[],by simp,rfl,rfl⟩
  | @cons p u q hadj walk ih =>
    obtain ⟨d,rfl⟩ := (companion_adj_iff p u).mp hadj
    obtain ⟨ds,he,hc,hedges⟩ := ih
    refine ⟨d::ds,by simpa [add_assoc] using he,?_,?_⟩
    · simp only [pathCost,GammaFPP.LoopGraph.pathCost_cons,GammaFPP.LoopGraph.edgeCost,hc]
      rw [← companionEdge_step,companionWeights_edge]
    · simp only [trace,List.map_cons,traversalEdge,companionEdge_step,SimpleGraph.Walk.edges_cons]
      simpa only [traversalEdge,companionEdge_step] using congrArg (List.cons s(p,p+d.delta)) hedges

/-- Loop erasure in the exact original path model, for arbitrary endpoints
and nonnegative real weights. It never increases cost. -/
theorem erase_path_loops (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e) (p : Vertex) (ds : List Step) :
    ∃ es : List Step, displacement es=displacement ds ∧
      ((trace p es).map traversalEdge).Nodup ∧ pathCost w p es ≤ pathCost w p ds := by
  obtain ⟨walk,hcost⟩ := steps_companion_walk w p ds
  obtain ⟨es,hend,hc,he⟩ := companion_walk_steps_edges w walk.bypass
  have hn := walk.bypass_isPath.isTrail.edges_nodup
  rw [← he] at hn
  have hn' : (((trace p es).map traversalEdge).map (fun e => (companionEdge e).val)).Nodup := by
    simpa only [List.map_map,Function.comp_def] using hn
  refine ⟨es,add_left_cancel hend,List.Nodup.of_map _ hn',?_⟩
  rw [hc,← hcost]
  exact GammaFPP.LoopGraph.bypass_cost_le (companionWeights w) (fun e => hw _) walk

end GammaFPP.LoopErase

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MeanNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory PlanarFPP Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Literal Euclidean-plane pullback of the actual mean seminorm. -/
noncomputable def gammaMeanNorm
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (v : Plane) : ℝ := gammaMeanPairSeminorm h hs hr (v 0, v 1)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MeanSwap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Filter Topology PlanarFPP

namespace SwapGeometry

def swapStep : Step → Step
  | .east => .north
  | .west => .south
  | .north => .east
  | .south => .west

@[simp] lemma swapStep_swap (d : Step) : swapStep (swapStep d)=d := by cases d <;> rfl
@[simp] lemma swapStep_delta (d : Step) : (swapStep d).delta=d.delta.swap := by cases d <;> rfl

def swapEdge (e : Edge) : Edge := (e.1.swap,!e.2)
@[simp] lemma swapEdge_swap (e : Edge) : swapEdge (swapEdge e)=e := by rcases e with ⟨p,b⟩; cases b <;> rfl

end SwapGeometry

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_AnalyticSpecialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.Analytic
open PlanarFPP Set MeasureTheory

/-- The slope wedge used by the manuscript's probabilistic argument. -/
def NoCornerWedge (μ : Plane → ℝ) : Prop :=
  ∀ b : ℝ, |b| ≤ 1 →
    leftSlope (fun t : ℝ => μ (direction b + t • transverseUnit)) =
      rightSlope (fun t : ℝ => μ (direction b + t • transverseUnit))

end GammaFPP.Analytic

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BKFamilies
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset
variable {α : Type*} [DecidableEq α]

def UpwardFamily (s : Finset α) (A : Finset (Finset α)) : Prop :=
  (∀ x ∈ A, x ⊆ s) ∧ ∀ x ∈ A, ∀ y, x ⊆ y → y ⊆ s → y ∈ A

noncomputable def disjointOccurrenceFamily (s : Finset α) (A B : Finset (Finset α)) : Finset (Finset α) :=
  by
    classical
    exact s.powerset.filter (fun x => ∃ a ∈ A, ∃ b ∈ B, a ⊆ x ∧ b ⊆ x ∧ Disjoint a b)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BKRepeated
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset
variable {α : Type*} [DecidableEq α]

/-- Uniform measure on the Boolean cube with ground set `s`. -/
noncomputable def fairFamilyMass (s : Finset α) (A : Finset (Finset α)) : ℝ :=
  A.card / (2:ℝ)^s.card

noncomputable def iteratedDisjointOccurrence (s : Finset α) : List (Finset (Finset α)) → Finset (Finset α)
  | [] => s.powerset
  | A :: As => disjointOccurrenceFamily s A (iteratedDisjointOccurrence s As)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_DyadicRanks
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open Finset PlanarFPP

/-- Positions of the zero bits, numbered from the least significant end. -/
noncomputable def dyadicPositions (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) : Finset ℕ :=
  ((univ : Finset (Fin t)).filter (fun h => (e,h) ∈ x)).image (fun h => t-(h.val+1))

noncomputable def dyadicRank (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) : ℕ :=
  ∑ a ∈ dyadicPositions t x e, 2^a

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CDF
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

variable {shape rate : ℝ}

lemma gamma_nullSingleton : NullSingletonClass (gammaMeasure shape rate) := by
  unfold gammaMeasure
  infer_instance

lemma gamma_cdf_continuous (hs : 0 < shape) (hr : 0 < rate) :
    Continuous (cdf (gammaMeasure shape rate)) := by
  let := isProbabilityMeasure_gammaMeasure hs hr
  let := gamma_nullSingleton (shape := shape) (rate := rate)
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (monotone_cdf (gammaMeasure shape rate)).continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [StieltjesFunction.rightLim_eq]
  have hzero : ENNReal.ofReal (cdf (gammaMeasure shape rate) x -
      Function.leftLim (cdf (gammaMeasure shape rate)) x) = 0 := by
    rw [← StieltjesFunction.measure_singleton, measure_cdf, measure_singleton]
  have hle := ENNReal.ofReal_eq_zero.mp hzero
  have hother := (monotone_cdf (gammaMeasure shape rate)).leftLim_le (le_refl x)
  linarith

lemma gamma_Ioc_pos (hs : 0 < shape) (hr : 0 < rate)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    0 < gammaMeasure shape rate (Ioc x y) := by
  have hmeas : Measurable (gammaPDF shape rate) :=
    (measurable_gammaPDFReal shape rate).ennreal_ofReal
  have hsupport : {z | gammaPDF shape rate z ≠ 0} ∩ Ioc x y = Ioc x y := by
    ext z
    constructor
    · exact fun h => h.2
    · intro hz
      refine ⟨?_, hz⟩
      exact ne_of_gt (ENNReal.ofReal_pos.mpr
        (gammaPDFReal_pos hs hr (lt_of_le_of_lt hx hz.1)))
  apply pos_iff_ne_zero.mpr
  intro hz
  have hv := (withDensity_apply_eq_zero hmeas).mp hz
  rw [hsupport, Real.volume_Ioc, ENNReal.ofReal_eq_zero] at hv
  linarith

lemma gamma_cdf_strictMonoOn (hs : 0 < shape) (hr : 0 < rate) :
    StrictMonoOn (cdf (gammaMeasure shape rate)) (Ici 0) := by
  let := isProbabilityMeasure_gammaMeasure hs hr
  intro x hx y _ hxy
  have hp := gamma_Ioc_pos hs hr hx hxy
  rw [← measure_cdf (gammaMeasure shape rate), StieltjesFunction.measure_Ioc,
    ENNReal.ofReal_pos] at hp
  exact sub_pos.mp hp

lemma gamma_cdf_zero (hs : 0 < shape) (hr : 0 < rate) :
    cdf (gammaMeasure shape rate) 0 = 0 := by
  let := isProbabilityMeasure_gammaMeasure hs hr
  let := gamma_nullSingleton (shape := shape) (rate := rate)
  have he : gammaMeasure shape rate (Iic 0) = gammaMeasure shape rate (Iio 0) :=
    (measure_congr Iio_ae_eq_Iic).symm
  have hz : gammaMeasure shape rate (Iio 0) = 0 := by
    rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
    exact lintegral_gammaPDF_of_nonpos (le_refl 0)
  rw [cdf_eq_real, measureReal_def, he, hz, ENNReal.toReal_zero]

/-- Every `u ∈ [0, 1)` has a unique nonnegative Gamma quantile. -/
lemma gamma_cdf_existsUnique (hs : 0 < shape) (hr : 0 < rate)
    {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
    ∃! x : ℝ, 0 ≤ x ∧ cdf (gammaMeasure shape rate) x = u := by
  have hev : ∀ᶠ b : ℝ in atTop, 0 ≤ b ∧ u < cdf (gammaMeasure shape rate) b := by
    filter_upwards [eventually_ge_atTop (0 : ℝ),
      (tendsto_cdf_atTop (gammaMeasure shape rate)).eventually (Ioi_mem_nhds hu1)]
      with b hb hbu
    exact ⟨hb, hbu⟩
  obtain ⟨b, hb, hbu⟩ := hev.exists
  have hu0 : cdf (gammaMeasure shape rate) 0 ≤ u := by
    rw [gamma_cdf_zero hs hr]
    exact hu
  obtain ⟨x, hx, hxu⟩ := intermediate_value_Icc hb
    (gamma_cdf_continuous hs hr).continuousOn ⟨hu0, hbu.le⟩
  refine ⟨x, ⟨hx.1, hxu⟩, ?_⟩
  intro y hy
  exact (gamma_cdf_strictMonoOn hs hr).injOn hy.1 hx.1 (hy.2.trans hxu.symm)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_Quantile
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable def gammaQuantileReal (shape rate : ℝ) (hs : 0 < shape) (hr : 0 < rate)
    (u : ℝ) : ℝ :=
  if h : 0 ≤ u ∧ u < 1 then
    Classical.choose (ExistsUnique.exists (gamma_cdf_existsUnique hs hr h.1 h.2))
  else 0

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SurvivalQuantile
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

variable {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate)

noncomputable def gammaSurvival (shape rate x : ℝ) : ℝ :=
  1 - cdf (gammaMeasure shape rate) x

noncomputable def gammaSurvivalQuantile (v : ℝ) : ℝ :=
  gammaQuantileReal shape rate hs hr (1 - v)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BKBitLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Set Finset Filter PlanarFPP
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}
variable {shape rate : ℝ}

def gammaDyadicRankCell (shape rate : ℝ) (τ : Edge → Ω → ℝ) (S : Finset Edge) (t : ℕ)
    (x : Finset (Edge × Fin t)) : Set Ω :=
  {ω | ∀ e ∈ S, ⌊(2:ℝ)^t*gammaSurvival shape rate (τ e ω)⌋₊ = dyadicRank t x e}

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BKForcing
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset
variable {α : Type*} [DecidableEq α]

/-- Fixing every bit in `c` to its value in `x` forces the event `A`. -/
def ForcesBits (s : Finset α) (A : Finset (Finset α)) (x c : Finset α) : Prop :=
  ∀ y ⊆ s, (∀ e ∈ c, e ∈ y ↔ e ∈ x) → y ∈ A

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GridIndependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint independence for finite families of tests on disjoint edge sets. -/
namespace GammaFPP.Grid
open PlanarFPP MeasureTheory ProbabilityTheory Set Finset

def DependsOnEdges (A : Set (Edge → ℝ)) (S : Finset Edge) : Prop :=
  ∀ w w', (∀ e ∈ S, w e=w' e) → (w ∈ A ↔ w' ∈ A)

noncomputable def extendEdgeWeights (S : Finset Edge) (w : S → ℝ) : Edge → ℝ :=
  fun e => if he : e ∈ S then w ⟨e,he⟩ else 0

end GammaFPP.Grid

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_RealDirectionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.RealDirectionBridge
open PlanarFPP MeasureTheory Filter Set
open scoped Topology

noncomputable def latticeEmbed (z : Vertex) : Plane :=
  WithLp.toLp 2 ![(z.1 : ℝ), (z.2 : ℝ)]

@[simp] theorem latticeEmbed_zero : latticeEmbed 0 = 0 := by ext i; fin_cases i <;> simp [latticeEmbed]
@[simp] theorem latticeFloor_embed (z : Vertex) : latticeFloor (latticeEmbed z) = z := by
  simp [latticeFloor, latticeEmbed]

@[simp] theorem latticeEmbed_sub (z w : Vertex) :
    latticeEmbed (z-w) = latticeEmbed z - latticeEmbed w := by
  ext i
  fin_cases i <;> simp [latticeEmbed]

noncomputable def scaledLatticePoint (t : ℝ) (p : Vertex) : Plane :=
  (1/t) • latticeEmbed p

end GammaFPP.RealDirectionBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CoordinateTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Finset
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- A linear allowance depending on the Gamma shape and rate. -/
noncomputable def coordinateAllowance (shape rate : ℝ) : ℝ := 2 * (shape + 1) / rate

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_TiltDensity
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

/-- Likelihood for changing a Gamma rate from `rate` to `rate / alpha`. -/
noncomputable def gammaScaleLikelihood (shape rate alpha x : ℝ) : ℝ :=
  alpha ^ (-shape) * exp (-(rate * (alpha⁻¹ - 1)) * x)

/-- The likelihood with the parametrization `alpha = 1 - delta`. -/
noncomputable def gammaShrinkLikelihood (shape rate delta x : ℝ) : ℝ :=
  gammaScaleLikelihood shape rate (1 - delta) x

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SpatialModulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP

open MeasureTheory ProbabilityTheory PlanarFPP Finset Filter Set
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Failure of the Gamma allowance for some actual coordinate path in the box. -/
def gammaBadConnections (shape rate : ℝ) (τ : Edge → Ω → ℝ)
    (ε : ℝ) (n : ℕ) : Set Ω :=
  ⋃ pq ∈ (latticeBox n) ×ˢ (latticeBox n),
    {ω | coordinateAllowance shape rate * (latticeDistance pq.1 pq.2 : ℝ) + ε * n ≤
      pathCost (fun e => τ e ω) pq.1 (coordinatePath pq.1 pq.2)}

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ConcentrationScale
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.FiniteLocal

noncomputable def concentrationKappa (shape rate : ℝ) : ℝ :=
  min (rate/4) (1/(4*((16*(2 : ℝ)^shape/rate^2)+1)))

end GammaFPP.FiniteLocal

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_TiltMoment
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

noncomputable def squareTheta (rate delta : ℝ) : ℝ :=
  -(2 * rate * ((1 - delta)⁻¹ - 1))

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_FiniteTilt
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP

open Set Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι]

/-- The iid Gamma law on a finite set of coordinates. -/
noncomputable def finiteGammaMeasure (shape rate : ℝ) : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => gammaMeasure shape rate)

/-- Product likelihood for coordinatewise scaling by `a`. -/
noncomputable def finiteGammaScaleLikelihood (shape rate a : ℝ) (x : ι → ℝ) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (gammaScaleLikelihood shape rate a (x i))

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_LocalTrailCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.FiniteLocal
open PlanarFPP

/-- A path with unit edge weights has cost equal to its number of steps. -/
lemma pathCost_one_eq_length (p : Vertex) (ds : List Step) :
    pathCost (fun _ : Edge => (1 : ℝ)) p ds = (ds.length : ℝ) := by
  induction ds generalizing p with
  | nil => simp [pathCost]
  | cons d ds ih =>
      simp [pathCost, ih, Nat.cast_add, Nat.cast_one, add_comm]

/-- The coordinate path has length equal to the lattice distance. -/
lemma coordinatePath_length (p q : Vertex) :
    (coordinatePath p q).length = latticeDistance p q := by
  have hh (a : ℤ) : (horizontal a).length = a.natAbs := by
    unfold horizontal
    split_ifs <;> simp only [List.length_replicate] <;> omega
  have hv (a : ℤ) : (vertical a).length = a.natAbs := by
    unfold vertical
    split_ifs <;> simp only [List.length_replicate] <;> omega
  simp [coordinatePath, latticeDistance, hh, hv]

/-- Loop erasure at unit weights produces a trail of at most the lattice distance. -/
lemma exists_short_trail (p q : Vertex) :
    ∃ ds : List Step, p + displacement ds = q ∧
      ((trace p ds).map traversalEdge).Nodup ∧ ds.length ≤ latticeDistance p q := by
  obtain ⟨ds, he, hn, hc⟩ := LoopErase.erase_path_loops
    (fun _ : Edge => (1 : ℝ)) (fun _ => zero_le_one) p (coordinatePath p q)
  have hend : p + displacement ds = q := by
    rw [he, coordinatePath_endpoint]
  rw [pathCost_one_eq_length, pathCost_one_eq_length, coordinatePath_length] at hc
  have hlen : ds.length ≤ latticeDistance p q := by exact_mod_cast hc
  exact ⟨ds, hend, hn, hlen⟩

/-- Trails with fewer than `R` steps connecting the specified endpoints. -/
noncomputable def candidates (p q : Vertex) (R : ℕ) : Finset (List Step) := by
  classical
  exact ((Finset.range R).biUnion (fixedTrailLists p)).filter
    (fun ds => p + displacement ds = q)

lemma mem_candidates (p q : Vertex) (R : ℕ) (ds : List Step) :
    ds ∈ candidates p q R ↔ p + displacement ds = q ∧
      ((trace p ds).map traversalEdge).Nodup ∧ ds.length < R := by
  classical
  constructor
  · intro h
    obtain ⟨hunion, hend⟩ := Finset.mem_filter.mp h
    obtain ⟨n, hn, htrail⟩ := Finset.mem_biUnion.mp hunion
    obtain ⟨hlen, hnodup⟩ := (mem_fixedTrailLists p n ds).mp htrail
    refine ⟨hend, hnodup, ?_⟩
    simpa only [hlen] using (Finset.mem_range.mp hn)
  · rintro ⟨hend, hnodup, hlen⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hend⟩
    exact Finset.mem_biUnion.mpr ⟨ds.length, Finset.mem_range.mpr hlen,
      (mem_fixedTrailLists p ds.length ds).mpr ⟨rfl, hnodup⟩⟩

lemma candidates_nonempty (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) : (candidates p q R).Nonempty := by
  obtain ⟨ds, hend, hnodup, hlen⟩ := exists_short_trail p q
  exact ⟨ds, (mem_candidates p q R ds).mpr ⟨hend, hnodup, hlen.trans_lt hR⟩⟩

end GammaFPP.FiniteLocal

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_LocalTrailPassage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.FiniteLocal
open PlanarFPP

/-- Costs of trails in the finite candidate family. -/
def costs (w : Edge → ℝ) (p q : Vertex) (R : ℕ) : Set ℝ :=
  {c | ∃ ds ∈ candidates p q R, c = pathCost w p ds}

/-- The infimum of costs among candidate trails. It is a finite minimum whenever
the lattice distance is less than `R`. -/
noncomputable def passageTime (w : Edge → ℝ) (p q : Vertex) (R : ℕ) : ℝ :=
  sInf (costs w p q R)

end GammaFPP.FiniteLocal

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_LocalResamplingModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.FiniteLocal
open PlanarFPP Finset

noncomputable def localEdges (p q : Vertex) (R : ℕ) : Finset Edge := by
  classical
  exact (candidates p q R).biUnion (fun ds => ((trace p ds).map traversalEdge).toFinset)

abbrev Coordinates (p q : Vertex) (R : ℕ) := (e : ↥(localEdges p q R)) → ℝ

noncomputable def extend (p q : Vertex) (R : ℕ) (v : Coordinates p q R) : Edge → ℝ := by
  classical
  exact fun e => if he : e ∈ localEdges p q R then v ⟨e, he⟩ else 0

@[simp] lemma extend_apply (p q : Vertex) (R : ℕ) (v : Coordinates p q R)
    (e : ↥(localEdges p q R)) : extend p q R v e = v e := by
  classical
  simp [extend, e.property]

noncomputable def finitePassageTime (p q : Vertex) (R : ℕ)
    (v : Coordinates p q R) : ℝ := passageTime (extend p q R v) p q R

/-- Upward change in the exact finite candidate infimum. -/
noncomputable def upward (w : Edge → ℝ) (p q : Vertex) (R : ℕ)
    (e : Edge) (u : ℝ) : ℝ := by
  classical
  exact max (passageTime (Function.update w e u) p q R - passageTime w p q R) 0

end GammaFPP.FiniteLocal

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.LatticePassage_FiniteVariance
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Finset

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

noncomputable def coordinateVariance {ι : Type*} [DecidableEq ι]
    (f : (ι → α) → ℝ) (i : ι) (v : ι → α) : ℝ :=
  variance (fun u => f (Function.update v i u)) μ

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.LatticePassage_ResamplingSymmetry
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
  (μ : Measure α) [IsProbabilityMeasure μ]

noncomputable def exchangeCoordinate (i : ι) (z : (ι → α) × (ι → α)) :
    (ι → α) × (ι → α) :=
  (Function.update z.1 i (z.2 i), Function.update z.2 i (z.1 i))

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.LatticePassage_EfronStein
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped ENNReal

def clipReal (n : ℕ) (a : ℝ) : ℝ := max (-(n : ℝ)) (min a n)

@[fun_prop] lemma measurable_clipReal (n : ℕ) : Measurable (clipReal n) := by
  unfold clipReal
  fun_prop

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_PathSecondMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Finset
open scoped BigOperators

noncomputable def pathSecondMomentConstant (shape rate : ℝ) : ℝ :=
  8 * (2 : ℝ)^shape / rate^2

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GlobalConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Real

noncomputable def localizationErrorBound (shape rate : ℝ) (d R : ℕ) : ℝ :=
  (1/2 : ℝ)^R + 2*exp (-(rate/4) *
    (cheapSlope shape rate*(R : ℝ)-coordinateAllowance shape rate*(d : ℝ)))

noncomputable def meanLocalizationAllowance (shape rate : ℝ) (d R : ℕ) : ℝ :=
  sqrt (pathSecondMomentConstant shape rate*(d : ℝ)^2) *
    sqrt (localizationErrorBound shape rate d R)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SequenceSummability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory Real Filter Topology PlanarFPP

noncomputable def localizationDecay (shape rate : ℝ) : ℝ :=
  min (log 2) (rate*cheapSlope shape rate/8)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_UniformShapeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.UniformShapeBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory Filter Set Metric
open scoped Topology

noncomputable def rescaledPassage (w : Edge → ℝ) (n : ℕ) (v : Plane) : ℝ :=
  passageTime w 0 (latticeFloor ((n : ℝ) • v)) / n

/-- Uniform shape convergence gives the epsilon-radius estimate for all
lattice endpoints inside a linearly growing ball. -/
def UniformShape (w : Edge → ℝ) (μ : Plane → ℝ) : Prop :=
  ∀ ε > 0, ∃ R : ℝ, 0 < R ∧ ∀ z : Vertex, R ≤ ‖latticeEmbed z‖ →
    |passageTime w 0 z-μ (latticeEmbed z)| ≤ ε * ‖latticeEmbed z‖

end GammaFPP.UniformShapeBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_OriginEscape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.UniformShapeBridge
open MeasureTheory Filter Set
open scoped Topology

/-- Every vertex of a finite path, including the final vertex, is tested. -/
def PathIn (p : Vertex) (ds : List Step) (S : Set Vertex) : Prop :=
  ∀ i ≤ ds.length, p+displacement (ds.take i) ∈ S

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CrossingLocalized
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set Finset MeasureTheory ProbabilityTheory

abbrev PathIn := IntervalTravelBridge.PathIn
abbrev DependsOnEdges := Grid.DependsOnEdges

@[simp] theorem pathIn_iff_interval (p : Vertex) (ds : List Step) (S : Set Vertex) :
    PathIn p ds S ↔ IntervalTravelBridge.PathIn p ds S := Iff.rfl
@[simp] theorem depends_iff_grid (A : Set (Edge → ℝ)) (S : Finset Edge) :
    DependsOnEdges A S ↔ Grid.DependsOnEdges A S := Iff.rfl

def edgeEnd (e : Edge) : Vertex := e.1 + if e.2 then (0,1) else (1,0)

def internalEdges (V : Finset Vertex) : Finset Edge :=
  (V ×ˢ Finset.univ).filter (fun e => edgeEnd e ∈ V)

def pathEdges (p : Vertex) : List Step → Finset Edge
  | [] => ∅
  | d::ds => insert (d.edge p) (pathEdges (p+d.delta) ds)

def strictLocalizedEvent (V : Finset Vertex) (family : Vertex → List Step → Prop)
    (bound : Vertex → List Step → ℝ) : Set (Edge → ℝ) :=
  {w | ∃ p ds, family p ds ∧ PathIn p ds (V : Set Vertex) ∧ pathCost w p ds < bound p ds}

def boundedLocalizedEvent (V : Finset Vertex) (family : Vertex → List Step → Prop)
    (bound : Vertex → List Step → ℝ) : Set (Edge → ℝ) :=
  {w | ∃ p ds, family p ds ∧ PathIn p ds (V : Set Vertex) ∧ pathCost w p ds ≤ bound p ds}

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BKPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.BK
open PlanarFPP Finset

/-- The same physical support used by the crossing and spatial events. -/
abbrev pathEdges := GammaFPP.CrossingBridge.pathEdges

@[simp] theorem pathEdges_eq_crossing (p : Vertex) (ds : List Step) :
    pathEdges p ds = GammaFPP.CrossingBridge.pathEdges p ds := rfl

/-- A labelled strict finite path. Different bounds on the same path are
retained as different witnesses. -/
structure StrictPathWitness where
  start : Vertex
  steps : List Step
  bound : ℝ

namespace StrictPathWitness

def edges (p : StrictPathWitness) : Finset Edge := pathEdges p.start p.steps

def bits (p : StrictPathWitness) (t : ℕ) : Finset (Edge × Fin t) := p.edges ×ˢ univ

end StrictPathWitness

/-- The bits in `x` are the zero bits of the manuscript's uniform expansion.
This is exactly 1-U^(t); zero is the cell whose rounded cost is infinity. -/
noncomputable def dyadicSurvival (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) : ℝ :=
  ∑ h : Fin t, if (e,h) ∈ x then 1/(2:ℝ)^(h.val+1) else 0

def StrictPathWitness.Good (w : Edge → ℝ) (p : StrictPathWitness) : Prop :=
  pathCost w p.start p.steps < p.bound

/-- Original strict witnesses with pairwise disjoint physical edge supports. -/
def StrictDisjointPaths (S : Finset Edge) (Fs : List (Set StrictPathWitness)) (w : Edge → ℝ) : Prop :=
  ∃ ps : List StrictPathWitness,
    List.Forall₂ (fun p F => p ∈ F ∧ p.edges ⊆ S ∧ p.Good w) ps Fs ∧
    ps.Pairwise (fun p q => Disjoint p.edges q.edges)

/-- Existence of a strict path witness with support in a prescribed finite edge set. -/
def StrictPathEvent (S : Finset Edge) (F : Set StrictPathWitness) (w : Edge → ℝ) : Prop :=
  ∃ p ∈ F, p.edges ⊆ S ∧ p.Good w

@[simp] theorem StrictPathWitness.edges_eq_crossing (p : StrictPathWitness) :
    p.edges = GammaFPP.CrossingBridge.pathEdges p.start p.steps := rfl

end GammaFPP.BK

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SurvivalRounding
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open Set Filter
open scoped Topology ENNReal
variable {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate)

noncomputable def gammaRoundedSurvival (t : ℕ) (x : ℝ) : ℝ :=
  (⌊(2 : ℝ)^t * gammaSurvival shape rate x⌋₊ : ℝ) / (2 : ℝ)^t

noncomputable def gammaRoundedCost (t : ℕ) (x : ℝ) : ℝ :=
  gammaSurvivalQuantile hs hr (gammaRoundedSurvival (shape := shape) (rate := rate) t x)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BKDyadic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.BK
open PlanarFPP Finset Set

/-- The guard implements infinity at zero; D's totalized value at zero is unused. -/
def BitGood (D : ℝ → ℝ) (t : ℕ) (x : Finset (Edge × Fin t))
    (p : StrictPathWitness) : Prop :=
  (∀ e ∈ p.edges, 0 < dyadicSurvival t x e) ∧
    pathCost (fun e => D (dyadicSurvival t x e)) p.start p.steps < p.bound

noncomputable def bitFamily (D : ℝ → ℝ) (S : Finset Edge) (t : ℕ)
    (F : Set StrictPathWitness) : Finset (Finset (Edge × Fin t)) := by
  classical
  exact (S.product (Finset.univ : Finset (Fin t))).powerset.filter
    (fun x => ∃ p ∈ F, p.edges ⊆ S ∧ BitGood D t x p)

noncomputable def bitDisjointFamily (D : ℝ → ℝ) (S : Finset Edge) (t : ℕ)
    (Fs : List (Set StrictPathWitness)) : Finset (Finset (Edge × Fin t)) := by
  classical
  exact (S.product (Finset.univ : Finset (Fin t))).powerset.filter (fun x =>
    ∃ ps : List StrictPathWitness,
      List.Forall₂ (fun p F => p ∈ F ∧ p.edges ⊆ S ∧ BitGood D t x p) ps Fs ∧
      ps.Pairwise (fun p q => Disjoint p.edges q.edges))

end GammaFPP.BK

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BKRounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.BK
open PlanarFPP MeasureTheory ProbabilityTheory Set Finset Filter
open scoped Topology ENNReal
variable {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate)

def RoundedGood (t : ℕ) (w : Edge → ℝ) (p : StrictPathWitness) : Prop :=
  (∀ e ∈ p.edges, 0 < gammaRoundedSurvival (shape := shape) (rate := rate) t (w e)) ∧
    pathCost (fun e => gammaRoundedCost hs hr t (w e)) p.start p.steps < p.bound

def RoundedDisjoint (S : Finset Edge) (Fs : List (Set StrictPathWitness))
    (t : ℕ) (w : Edge → ℝ) : Prop :=
  ∃ ps : List StrictPathWitness,
    List.Forall₂ (fun p F => p ∈ F ∧ p.edges ⊆ S ∧ RoundedGood hs hr t w p) ps Fs ∧
    ps.Pairwise (fun p q => Disjoint p.edges q.edges)

end GammaFPP.BK

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MovingOrigin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

def GoodOrigin (μ : Plane → ℝ) (α : ℝ) (C : ℕ) (η δ : ℝ) (n : ℕ)
    (w : Edge → ℝ) : Prop :=
  (∀ e, 0 ≤ w e) ∧
  (∀ z : Vertex, ‖latticeEmbed z‖ ≤ (C : ℝ)*n →
    |passageTime w 0 z-μ (latticeEmbed z)| ≤ η*n) ∧
  (∀ z : Vertex, δ*n/3 ≤ ‖latticeEmbed z‖ → α*δ*n/6 ≤ passageTime w 0 z)

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_Waypoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Set Finset Filter
open scoped Topology

noncomputable def segmentPoint (p q : Vertex) (t : ℝ) : Plane :=
  latticeEmbed p+t • (latticeEmbed q-latticeEmbed p)

noncomputable def waypoint (p q : Vertex) (B j : ℕ) : Vertex :=
  latticeFloor (segmentPoint p q ((j : ℝ)/B))

def SegmentTube (p q : Vertex) (R : ℝ) : Set Vertex :=
  {z | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ‖latticeEmbed z-segmentPoint p q t‖ ≤ R}

@[simp] theorem waypoint_zero (p q : Vertex) (B : ℕ) : waypoint p q B 0=p := by
  simp [waypoint,segmentPoint]

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_TubeDeterministic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Set Finset Filter
open scoped Topology

def LocalTravel (μ : Plane → ℝ) (η δ s : ℝ) (p q : Vertex) (w : Edge → ℝ) : Prop :=
  ∃ ds, p+displacement ds=q ∧ pathCost w p ds ≤ μ (latticeEmbed (q-p))+η*s ∧
    PathIn p ds (SegmentTube p q (δ*s))

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_EndpointNet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Set Finset Filter Metric
open scoped Topology

@[simp] theorem latticeEmbed_add (p q : Vertex) :
    latticeEmbed (p+q) = latticeEmbed p+latticeEmbed q := by
  ext i
  fin_cases i <;> simp [latticeEmbed]

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BallTravelGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Set Finset Filter Metric
open scoped Topology

def BallTravel (μ : Plane → ℝ) (D η δ s : ℝ) (w : Edge → ℝ) : Prop :=
  ∀ p q : Vertex, ‖latticeEmbed p‖ ≤ D*s → ‖latticeEmbed q‖ ≤ D*s →
    LocalTravel μ η δ s p q w

end GammaFPP.IntervalTravelBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BoundaryGeometry
attribute [-instance] _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The uncancelled, counterclockwise square sides in
crossings.tex:cr:oriented-paths. A dual vertex `p` represents the actual
point `p - (1/2,1/2)`, so the square at the primal site `q` has lower-left
corner `q` in these integer coordinates. -/
namespace PlanarFPP
open Finset

instance instFintypeStep : Fintype Step where
  elems := {Step.east, Step.west, Step.north, Step.south}
  complete d := by cases d <;> simp

def Step.left : Step → Step
  | .east => .north | .north => .west | .west => .south | .south => .east

def Step.right : Step → Step
  | .east => .south | .south => .west | .west => .north | .north => .east

def Step.outward (d : Step) : Vertex := d.right.delta

def Step.corner : Step → Vertex
  | .east => (0,0) | .north => (1,0) | .west => (1,1) | .south => (0,1)

abbrev SquareSide := Vertex × Step

def SquareSide.tail (e : SquareSide) : Vertex := e.1 + e.2.corner

def SquareSide.head (e : SquareSide) : Vertex := e.tail + e.2.delta

def IsBoundarySide (S : Finset Vertex) (e : SquareSide) : Prop :=
  e.1 ∈ S ∧ e.1 + e.2.outward ∉ S

instance instDecidableIsBoundarySide (S : Finset Vertex) (e : SquareSide) : Decidable (IsBoundarySide S e) :=
  inferInstanceAs (Decidable (_ ∧ _))

def boundarySides (S : Finset Vertex) : Finset SquareSide :=
  (S ×ˢ univ).filter (fun e => e.1 + e.2.outward ∉ S)

@[simp] theorem mem_boundarySides (S : Finset Vertex) (e : SquareSide) :
    e ∈ boundarySides S ↔ IsBoundarySide S e := by
  simp [boundarySides, IsBoundarySide]

/-- Follow the first uncancelled side counterclockwise around the arriving
corner. The two tests inspect the other two squares meeting that corner. -/
def boundaryNext (S : Finset Vertex) (e : SquareSide) : SquareSide :=
  let q := e.1
  let d := e.2
  let r := q + d.left.outward
  let t := r + d.outward
  if r ∉ S then (q,d.left) else if t ∉ S then (r,d) else (t,d.right)

def boundaryPrev (S : Finset Vertex) (e : SquareSide) : SquareSide :=
  let q := e.1
  let d := e.2
  let r := q + d.right.outward
  let t := r + d.outward
  if r ∉ S then (q,d.right) else if t ∉ S then (r,d) else (t,d.left)

theorem boundaryNext_boundary (S : Finset Vertex) (e : SquareSide)
    (he : IsBoundarySide S e) : IsBoundarySide S (boundaryNext S e) := by
  rcases e with ⟨⟨x,y⟩,d⟩
  unfold boundaryNext
  dsimp only
  split
  · cases d <;> simp_all [IsBoundarySide, Step.left, Step.outward, Step.right,
      Step.delta]
  · split
    · cases d <;> simp_all [IsBoundarySide, Step.left, Step.outward, Step.right,
        Step.delta]
    · cases d <;>
        simp_all [IsBoundarySide, Step.left, Step.outward, Step.right,
          Step.delta, Prod.mk_add_mk, add_assoc]

theorem boundaryPrev_next (S : Finset Vertex) (e : SquareSide)
    (he : IsBoundarySide S e) : boundaryPrev S (boundaryNext S e) = e := by
  rcases e with ⟨⟨x,y⟩,d⟩
  unfold boundaryNext
  dsimp only
  split
  · cases d <;>
      simp_all [boundaryPrev, IsBoundarySide, Step.left, Step.right,
        Step.outward, Step.delta, Prod.mk_add_mk]
  · split <;> cases d <;>
      simp_all [boundaryPrev, IsBoundarySide, Step.left, Step.right,
        Step.outward, Step.delta, Prod.mk_add_mk, add_assoc]

abbrev BoundarySide (S : Finset Vertex) := {e // e ∈ boundarySides S}

def boundarySuccessor (S : Finset Vertex) (e : BoundarySide S) : BoundarySide S :=
  ⟨boundaryNext S e.val, (mem_boundarySides S _).mpr
    (boundaryNext_boundary S e.val ((mem_boundarySides S _).mp e.property))⟩

theorem boundarySuccessor_injective (S : Finset Vertex) :
    Function.Injective (boundarySuccessor S) := by
  intro e f h
  apply Subtype.ext
  have hh := congrArg (fun a : BoundarySide S => boundaryPrev S a.val) h
  simpa only [boundarySuccessor, boundaryPrev_next S e.val
    ((mem_boundarySides S _).mp e.property), boundaryPrev_next S f.val
    ((mem_boundarySides S _).mp f.property)] using hh

/-- Cancellation of shared sides leaves a permutation of the remaining sides;
its cycles are directed closed walks with no repeated directed side. -/
noncomputable def boundaryPerm (S : Finset Vertex) : Equiv.Perm (BoundarySide S) :=
  Equiv.ofBijective (boundarySuccessor S)
    ⟨boundarySuccessor_injective S, Finite.surjective_of_injective
      (boundarySuccessor_injective S)⟩

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_BoundaryWinding
attribute [-instance] _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset

def SquareSide.rayCross (e : SquareSide) : ℤ :=
  match e.2 with
  | .north => if e.1.2 = 0 ∧ 0 ≤ e.1.1 then 1 else 0
  | .south => if e.1.2 = 0 ∧ 0 < e.1.1 then -1 else 0
  | _ => 0

def SquareSide.opposite (e : SquareSide) : SquareSide :=
  (e.1 + e.2.outward, e.2.reverse)

@[simp] theorem SquareSide.opposite_opposite (e : SquareSide) :
    e.opposite.opposite = e := by
  rcases e with ⟨⟨x,y⟩,d⟩
  cases d <;> simp [opposite, Step.outward, Step.right, Step.reverse, Step.delta]

@[simp] theorem SquareSide.rayCross_opposite (e : SquareSide) :
    e.opposite.rayCross = -e.rayCross := by
  rcases e with ⟨⟨x,y⟩,d⟩
  cases d <;> simp [opposite, rayCross, Step.outward, Step.right,
    Step.reverse, Step.delta] <;> split_ifs <;> omega

def internalSides (S : Finset Vertex) : Finset SquareSide :=
  (S ×ˢ univ).filter (fun e => e.1 + e.2.outward ∈ S)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ConnectorEvents
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge
open GammaFPP.IntervalTravelBridge Set MeasureTheory Filter
open scoped Topology

def allPairsRegionEvent (V : Finset Vertex) (I J : Set Vertex)
    (bound : Vertex → Vertex → ℝ) : Set (Edge → ℝ) :=
  {w | ∀ p ∈ I, ∀ q ∈ J, w ∈ boundedLocalizedEvent V
    (fun a ds => a=p ∧ a+displacement ds=q) (fun _ _ => bound p q)}

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_RareFastEvents
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set Finset MeasureTheory ProbabilityTheory
theorem finite_tilted_rectangle (b X Y L H : ℝ) :
    {p : Vertex | |(p.1 : ℝ)-X| ≤ L ∧ |transverse b p-Y| ≤ H}.Finite := by
  let B := |X|+|L|+|Y|+|H|+|b| *(|X|+|L|)
  obtain ⟨N,hN⟩ := exists_nat_gt B
  apply (Finset.finite_toSet (latticeBox N)).subset
  intro p hp
  obtain ⟨hpL,hpH⟩ := hp
  have hx : |(p.1 : ℝ)| ≤ |X|+|L| := by
    have hh := abs_add_le ((p.1 : ℝ)-X) X
    rw [sub_add_cancel] at hh
    linarith [le_abs_self L]
  have hy : |(p.2 : ℝ)| ≤ |Y|+|H|+|b| *(|X|+|L|) := by
    have hh := abs_add_le (transverse b p-Y) (Y+b*(p.1 : ℝ))
    have heq : transverse b p-Y+(Y+b*(p.1 : ℝ))=(p.2 : ℝ) := by unfold transverse; ring
    rw [heq] at hh
    have hh' := abs_add_le Y (b*(p.1 : ℝ))
    rw [abs_mul] at hh'
    have ht := mul_le_mul_of_nonneg_left hx (abs_nonneg b)
    linarith [le_abs_self H]
  have hxB : |(p.1 : ℝ)| < N := by
    dsimp [B] at hN
    nlinarith [abs_nonneg Y,abs_nonneg H,mul_nonneg (abs_nonneg b) (add_nonneg (abs_nonneg X) (abs_nonneg L))]
  have hyB : |(p.2 : ℝ)| < N := by
    dsimp [B] at hN
    linarith [abs_nonneg X,abs_nonneg L]
  have hx' : -(N : ℤ) ≤ p.1 ∧ p.1 ≤ N := by
    constructor
    · exact_mod_cast (abs_le.mp hxB.le).1
    · exact_mod_cast (abs_le.mp hxB.le).2
  have hy' : -(N : ℤ) ≤ p.2 ∧ p.2 ≤ N := by
    constructor
    · exact_mod_cast (abs_le.mp hyB.le).1
    · exact_mod_cast (abs_le.mp hyB.le).2
  change p ∈ latticeBox N
  simpa only [latticeBox,Finset.mem_product,Finset.mem_Icc] using And.intro hx' hy'

noncomputable def rareFastRegion (b A R s : ℝ) (n : ℤ) (t : Vertex) : Set Vertex :=
  {p | -A*(n : ℝ) ≤ ((p-t).1 : ℝ) ∧ ((p-t).1 : ℝ) ≤ (1+A)*n ∧
    |transverse b (p-t)| ≤ R*s}

theorem rareFastRegion_finite (b A R s : ℝ) (n : ℤ) (t : Vertex) :
    (rareFastRegion b A R s n t).Finite := by
  apply (finite_tilted_rectangle b t.1 (transverse b t)
    (|A*(n : ℝ)|+|(1+A)*(n : ℝ)|) (R*s)).subset
  intro p hp
  have htrans : transverse b (p-t)=transverse b p-transverse b t := by
    simp [transverse]; ring
  have hx : ((p-t).1 : ℝ)=(p.1 : ℝ)-t.1 := by simp
  refine ⟨abs_le.mpr ⟨?_,?_⟩,?_⟩
  · have := hp.1; rw [hx] at this
    linarith [le_abs_self (A*(n : ℝ)),abs_nonneg ((1+A)*(n : ℝ))]
  · have := hp.2.1; rw [hx] at this
    linarith [le_abs_self ((1+A)*(n : ℝ)),abs_nonneg (A*(n : ℝ))]
  · rw [← htrans]; exact hp.2.2

noncomputable def rareFastVertices (b A R s : ℝ) (n : ℤ) (t : Vertex) : Finset Vertex :=
  (rareFastRegion_finite b A R s n t).toFinset

@[simp] theorem mem_rareFastVertices (b A R s : ℝ) (n : ℤ) (t p : Vertex) :
    p ∈ rareFastVertices b A R s n t ↔ p ∈ rareFastRegion b A R s n t :=
  (rareFastRegion_finite b A R s n t).mem_toFinset

noncomputable def rareFastEvent (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) : Set (Edge → ℝ) :=
  strictLocalizedEvent (rareFastVertices b A R s n t)
    (fun p ds => p.1=t.1 ∧ (p+displacement ds).1=t.1+n)
    (fun _ ds => support b m a (displacement ds)-ε*s)

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ConnectorGeometry
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge Set

def connectorWindow (b : ℝ) (X : ℤ) (Y S : ℝ) : Set Vertex :=
  {p | p.1=X ∧ |transverse b p-Y| ≤ S/4}

def connectorRegion (b : ℝ) (X d : ℤ) (Y S s : ℝ) : Set Vertex :=
  {p | (X : ℝ)-s ≤ p.1 ∧ (p.1 : ℝ) ≤ (X : ℝ)+d+s ∧
    |transverse b p-Y| ≤ 4*S}

theorem connectorRegion_finite (b : ℝ) (X d : ℤ) (Y S s : ℝ) :
    (connectorRegion b X d Y S s).Finite := by
  apply (finite_tilted_rectangle b X Y (|(d : ℝ)|+|s|) (4*S)).subset
  intro p hp
  refine ⟨abs_le.mpr ⟨?_,?_⟩,hp.2.2⟩ <;>
    linarith [hp.1,hp.2.1,le_abs_self s,le_abs_self (d : ℝ),abs_nonneg (d : ℝ)]

noncomputable def connectorVertices (b : ℝ) (X d : ℤ) (Y S s : ℝ) : Finset Vertex :=
  (connectorRegion_finite b X d Y S s).toFinset

@[simp] theorem mem_connectorVertices (b : ℝ) (X d : ℤ) (Y S s : ℝ) (p : Vertex) :
    p ∈ connectorVertices b X d Y S s ↔ p ∈ connectorRegion b X d Y S s :=
  (connectorRegion_finite b X d Y S s).mem_toFinset

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SourceConnector
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge Set Filter MeasureTheory
open scoped Topology

noncomputable def trialSpacing (R s : ℝ) : ℝ := (R+1)*(⌈s⌉₊ : ℝ)
noncomputable def trialWindow (M : ℕ) (R s : ℝ) : ℝ := 100*M*trialSpacing R s

def contactSign (plus : Bool) : ℝ := if plus then 1 else -1

@[simp] theorem abs_contactSign (plus : Bool) : |contactSign plus|=1 := by
  cases plus <;> norm_num [contactSign]

noncomputable def sourceSupportCost (μ : Plane → ℝ) (b : ℝ) (plus : Bool)
    (ε s : ℝ) (p q : Vertex) : ℝ :=
  μ (direction b)*xCoord (latticeEmbed (q-p))+
    extremeSlope μ b plus*rCoord b (latticeEmbed (q-p))+ε*s/2

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GridGeometry
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.Grid
open PlanarFPP Finset

noncomputable def verticalIntervalEdges (X lo hi : ℤ) : Finset Edge :=
  (Finset.Ico lo hi).image (fun y => ((X,y),true))

noncomputable def transverseIntervalEdges (b : ℝ) (X : ℤ) (lo hi : ℝ) : Finset Edge :=
  verticalIntervalEdges X ⌈lo+b*X⌉ ⌊hi+b*X⌋

noncomputable def gridIntervalLower (h w : ℤ) : ℝ := (h : ℝ)*w-2
noncomputable def gridIntervalUpper (j : ℕ) (h w : ℤ) : ℝ :=
  (h : ℝ)*w+(30*(j : ℝ)^2+9)*w+2

end GammaFPP.Grid

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GridAttachments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.Grid
open PlanarFPP MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

noncomputable def verticalExponent (shape : ℝ) : ℝ := 50 * shape * (1 - Real.log 2)
noncomputable def attachmentAllowance (shape rate K : ℝ) : ℝ := K + 200 * shape / rate

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Finite-bin event with crossing trials and two whole attachment edge sets. -/
def binGood {ι : Type*} (trials : Finset ι) (A : ι → Set (Edge → ℝ))
    (S₁ S₂ : Finset Edge) (shape rate L : ℝ) : Set (Edge → ℝ) :=
  {weights | (∃ i ∈ trials, weights ∈ A i) ∧
    (∑ e ∈ S₁, weights e) ≤ 100 * shape / rate * L ∧
    (∑ e ∈ S₂, weights e) ≤ 100 * shape / rate * L}

end GammaFPP.Grid

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CrossingEvents
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set Finset MeasureTheory ProbabilityTheory
noncomputable def crossingEvent (b m K s : ℝ) (n : ℤ) (t : Vertex) : Set (Edge → ℝ) :=
  strictLocalizedEvent (rareFastVertices b 1 8 s n t)
    (fun p ds => p.1=t.1 ∧ (p+displacement ds).1=t.1+n)
    (fun _ _ => m*n+K*s)

noncomputable def gridTrialTranslate (b : ℝ) (X h w : ℤ) (t : ℕ) : Vertex :=
  (X,⌊b*X⌋+(h+30*(t+1 : ℕ))*w)

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- Grid-bin failure bound from a lower bound on the origin crossing
probability. -/
noncomputable def gridBinGood (shape rate b m K : ℝ) (X h w l : ℤ) (j : ℕ) :
    Set (Edge → ℝ) :=
  Grid.binGood Finset.univ
    (fun t : Fin (j^2) => crossingEvent b m K w l (gridTrialTranslate b X h w t))
    (Grid.transverseIntervalEdges b X (Grid.gridIntervalLower h w) (Grid.gridIntervalUpper j h w))
    (Grid.transverseIntervalEdges b (X+l) (Grid.gridIntervalLower h w) (Grid.gridIntervalUpper j h w))
    shape rate ((j : ℝ)^2*w)

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_FiniteEdgeTilt
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.Tilt
open PlanarFPP Set Finset MeasureTheory ProbabilityTheory

open GammaFPP.Grid

noncomputable def scaleFiniteEdges (S : Finset Edge) (α : ℝ) (w : Edge → ℝ) : Edge → ℝ :=
  fun e => if e ∈ S then α*w e else w e

end GammaFPP.Tilt

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_TiltRegionCount
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set Finset

noncomputable def tiltColumn (b s : ℝ) (x : ℤ) : Finset Vertex :=
  {x} ×ˢ Finset.Icc ⌈b*x-8*s⌉ ⌊b*x+8*s⌋

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_OrientedSelection
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Greedy extraction of separated sites from square-lattice contours. -/
namespace PlanarFPP
open Finset Set

noncomputable def orientedSelectionBox (n : ℕ) : Finset Vertex :=
  (Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (-(n : ℤ)) n)

def latticeNear (k : ℕ) (p q : Vertex) : Prop :=
  (q.1-p.1).natAbs ≤ k ∧ (q.2-p.2).natAbs ≤ k

instance instDecidableLatticeNear (k : ℕ) (p q : Vertex) : Decidable (latticeNear k p q) :=
  inferInstanceAs (Decidable (_ ∧ _))

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SquareLoops
attribute [-instance] _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Indexed square-lattice loops, their closedness count, and bad-site count. -/
namespace PlanarFPP
open Finset

structure SquareLoop (m : ℕ) where
  side : Fin m → SquareSide
  follows : ∀ i, (side (finRotate m i)).tail = (side i).head

namespace SquareLoop
variable {m : ℕ}

def winding (c : SquareLoop m) : ℤ := ∑ i, (c.side i).rayCross

def NoRepeatedSides (c : SquareLoop m) : Prop := Function.Injective c.side

def upLeftIndices (c : SquareLoop m) : Finset (Fin m) :=
  univ.filter (fun i => (c.side i).2 = Step.north ∨ (c.side i).2 = Step.west)

def badSites (c : SquareLoop m) : Finset Vertex :=
  c.upLeftIndices.image (fun i => (c.side i).1)

end SquareLoop

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ContourLocalization
attribute [-instance] _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A loop with nonzero ray-crossing count starts within O(m) of zero.
This supplies the location factor in the source's contour enumeration. -/
namespace PlanarFPP
open Finset

namespace SquareSide

def axisCross (e : SquareSide) : ℤ :=
  match e.2 with
  | .north => if e.1.2 = 0 then 1 else 0
  | .south => if e.1.2 = 0 then -1 else 0
  | _ => 0

def aboveAxis (p : Vertex) : ℤ := if 0 < p.2 then 1 else 0

theorem axisCross_eq (e : SquareSide) :
    e.axisCross = aboveAxis e.head - aboveAxis e.tail := by
  rcases e with ⟨⟨x,y⟩,d⟩
  cases d <;> simp [axisCross, aboveAxis, head, tail, Step.corner, Step.delta] <;>
    split_ifs <;> omega

theorem rayCross_eq_axisCross (e : SquareSide) (hx : 0 < e.tail.1) :
    e.rayCross = e.axisCross := by
  rcases e with ⟨⟨x,y⟩,d⟩
  cases d <;> simp_all [rayCross, axisCross, tail, Step.corner]
  all_goals (split_ifs <;> omega)

theorem rayCross_ne_zero_location (e : SquareSide) (he : e.rayCross ≠ 0) :
    0 < e.tail.1 ∧ 0 ≤ e.tail.2 ∧ e.tail.2 ≤ 1 := by
  rcases e with ⟨⟨x,y⟩,d⟩
  cases d <;> simp_all [rayCross, tail, Step.corner]
  all_goals omega

end SquareSide

namespace SquareLoop
variable {m : ℕ}

theorem sum_axisCross (c : SquareLoop m) : ∑ i, (c.side i).axisCross = 0 := by
  simp_rw [SquareSide.axisCross_eq, ← c.follows]
  rw [sum_sub_distrib, Equiv.sum_comp (finRotate m)
    (fun i => SquareSide.aboveAxis (c.side i).tail), sub_self]

theorem winding_locations (c : SquareLoop m) (hc : c.winding ≠ 0) :
    (∃ i, (c.side i).tail.1 ≤ 0) ∧
    (∃ i, 0 < (c.side i).tail.1 ∧ 0 ≤ (c.side i).tail.2 ∧ (c.side i).tail.2 ≤ 1) := by
  constructor
  · by_contra hn
    push Not at hn
    apply hc
    change (∑ i, (c.side i).rayCross) = 0
    simp_rw [SquareSide.rayCross_eq_axisCross _ (hn _)]
    exact c.sum_axisCross
  · have he : ∃ i, (c.side i).rayCross ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hc (sum_eq_zero (fun i _ => hn i))
    obtain ⟨i,hi⟩ := he
    exact ⟨i,SquareSide.rayCross_ne_zero_location _ hi⟩

theorem tail_bounds (c : SquareLoop m) (hm : 0 < m) (i : Fin m) :
    (c.side ⟨0,hm⟩).tail.1 - i.val ≤ (c.side i).tail.1 ∧
    (c.side i).tail.1 ≤ (c.side ⟨0,hm⟩).tail.1 + i.val ∧
    (c.side ⟨0,hm⟩).tail.2 - i.val ≤ (c.side i).tail.2 ∧
    (c.side i).tail.2 ≤ (c.side ⟨0,hm⟩).tail.2 + i.val := by
  have : NeZero m := ⟨Nat.ne_of_gt hm⟩
  obtain ⟨i,hi⟩ := i
  induction i with
  | zero => simp
  | succ n ih =>
    have hn : n < m := by omega
    have hh := c.follows ⟨n,hn⟩
    have hr : finRotate m ⟨n,hn⟩ = ⟨n+1,hi⟩ := by
      apply Fin.ext
      simp only [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
      exact Nat.mod_eq_of_lt hi
    rw [hr, SquareSide.head] at hh
    have hx := congrArg Prod.fst hh
    have hy := congrArg Prod.snd hh
    have ihh := ih hn
    cases hd : (c.side ⟨n,hn⟩).2 <;>
      simp [hd,Step.delta] at hx hy <;> dsimp only at * <;> omega

/-- With the source's length m, every enclosing loop has a permitted starting
point in a deterministic box of cardinality (2m+3)^2. -/
theorem start_mem_box (c : SquareLoop m) (hm : 0 < m) (hc : c.winding ≠ 0) :
    (c.side ⟨0,hm⟩).tail ∈ orientedSelectionBox (m+1) := by
  obtain ⟨⟨i,hi⟩,⟨j,hj0,hj1,hj2⟩⟩ := c.winding_locations hc
  have hbi := c.tail_bounds hm i
  have hbj := c.tail_bounds hm j
  have hi' := i.isLt
  have hj' := j.isLt
  simp only [orientedSelectionBox, mem_product, mem_Icc]
  constructor <;> constructor <;> omega

end SquareLoop

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ContourEnumeration
attribute [-instance] _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit C(m+1)^2 4^m encoding bound from cr:oriented-paths. -/
namespace PlanarFPP
open Finset

namespace SquareLoop
variable {m : ℕ}

theorem eq_of_start_direction (c d : SquareLoop m) (hm : 0 < m)
    (h0 : (c.side ⟨0,hm⟩).tail = (d.side ⟨0,hm⟩).tail)
    (hd : ∀ i, (c.side i).2 = (d.side i).2) : c = d := by
  have : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hp (i : Fin m) : (c.side i).tail = (d.side i).tail := by
    obtain ⟨n,hn⟩ := i
    induction n with
    | zero => exact h0
    | succ n ih =>
      have hn' : n < m := by omega
      have hr : finRotate m ⟨n,hn'⟩ = ⟨n+1,hn⟩ := by
        apply Fin.ext
        simp only [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
        exact Nat.mod_eq_of_lt hn
      have hc := c.follows ⟨n,hn'⟩
      have hh := d.follows ⟨n,hn'⟩
      rw [hr] at hc hh
      rw [hc,hh,SquareSide.head,SquareSide.head,ih hn',hd]
  have he : c.side = d.side := by
    funext i
    apply Prod.ext
    · have hh := hp i
      change (c.side i).1 + (c.side i).2.corner =
        (d.side i).1 + (d.side i).2.corner at hh
      rw [hd] at hh
      exact add_right_cancel hh
    · exact hd i
  cases c
  cases d
  cases he
  rfl

end SquareLoop

/-- Length n+1 avoids a spurious zero-length contour in the countable union. -/
abbrev EnclosingLoop (n : ℕ) :=
  {c : SquareLoop (n+1) // c.winding ≠ 0 ∧ c.NoRepeatedSides}

def enclosingLoopCode (n : ℕ) (c : EnclosingLoop n) :
    {p // p ∈ orientedSelectionBox (n+2)} × (Fin (n+1) → Step) :=
  (⟨(c.val.side ⟨0,by omega⟩).tail,c.val.start_mem_box (by omega) c.property.1⟩,
    fun i => (c.val.side i).2)

theorem enclosingLoopCode_injective (n : ℕ) : Function.Injective (enclosingLoopCode n) := by
  intro c d h
  apply Subtype.ext
  apply SquareLoop.eq_of_start_direction c.val d.val (by omega)
  · exact congrArg (fun x => x.1.val) h
  · intro i
    exact congrArg (fun x => x.2 i) h

noncomputable instance enclosingLoopFintype (n : ℕ) : Fintype (EnclosingLoop n) :=
  Fintype.ofInjective (enclosingLoopCode n) (enclosingLoopCode_injective n)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_OrientedCompactness
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite branching for oriented square-lattice paths. -/
namespace PlanarFPP
open Set Finset MeasureTheory

/-- n forward steps with all visited sites except possibly the last good. -/
def orientedSurvival (G : Vertex → Prop) (p : Vertex) : ℕ → Prop
  | 0 => True
  | n+1 => G p ∧ (orientedSurvival G (p+(1,0)) n ∨ orientedSurvival G (p+(0,1)) n)

def infiniteOrientedPath (G : Vertex → Prop) (p : Vertex) : Prop :=
  ∃ z : ℕ → Vertex, z 0=p ∧
    (∀ n, z (n+1)=z n+(1,0) ∨ z (n+1)=z n+(0,1)) ∧ ∀ n, G (z n)

noncomputable def orientedEndpoints (G : Vertex → Prop) (p : Vertex) : ℕ → Finset Vertex := by
  classical
  exact fun n => match n with
  | 0 => {p}
  | n+1 => if G p then orientedEndpoints G (p+(1,0)) n ∪ orientedEndpoints G (p+(0,1)) n else ∅

/-- The reachable set includes a possibly bad terminal site, exactly as in
the manuscript's S. This is the finite set to which its contour argument applies. -/
def orientedReachable (G : Vertex → Prop) (p : Vertex) : Set Vertex :=
  ⋃ n : ℕ, (orientedEndpoints G p n : Set Vertex)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_OrientedProbability
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dependent high-density bound in crossings.tex:cr:oriented-paths.
The tests need not be stationary. -/
namespace PlanarFPP
open Finset Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

def SeparatedGoodIndependent (P : Measure Ω) (G : Vertex → Set Ω) (k : ℕ) : Prop :=
  ∀ T : Finset Vertex,
    Set.Pairwise (↑T : Set Vertex) (fun p q => ¬latticeNear k p q) →
    iIndepSet (fun q : T => G q.val) P

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_HighDensityOriented
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full high-density oriented-path lemma, crossings.tex:cr:oriented-paths. -/
namespace PlanarFPP
open Finset Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

def badContourEvent (G : Vertex → Set Ω) {n : ℕ} (c : EnclosingLoop n) : Set Ω :=
  {ω | ∀ v ∈ c.val.badSites, ω ∉ G v}

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ShapeDeficit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Filter MeasureTheory
open scoped Topology

abbrev UniformShape := UniformShapeBridge.UniformShape

@[simp] theorem uniformShape_iff_gamma (w : Edge → ℝ) (μ : Plane → ℝ) :
    UniformShape w μ ↔ UniformShapeBridge.UniformShape w μ := Iff.rfl

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CrossingChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Filter MeasureTheory
open scoped Topology

def crossingChain (initialPath : List Step) (trial connector : ℕ → List Step) : ℕ → List Step
  | 0 => initialPath ++ trial 0
  | n+1 => crossingChain initialPath trial connector n ++ (connector n ++ trial (n+1))

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GoodSiteBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

def blockLayer (v : Vertex) : ℤ := v.1+v.2

def blockLevel (v : Vertex) : ℤ := v.1+2*v.2

def blockX (n d : ℤ) (v : Vertex) : ℤ := blockLayer v*(n+d)

noncomputable def blockY (σ S : ℝ) (v : Vertex) : ℝ := σ*(blockLevel v : ℝ)*S

noncomputable def blockRegion (b A : ℝ) (n d : ℤ) (σ S : ℝ) (v : Vertex) : Set Vertex :=
  {p | |(p.1 : ℝ)-(blockX n d v : ℝ)| ≤ (A+3)*n ∧
    |transverse b p-blockY σ S v| ≤ 4*S}

theorem blockRegion_finite (b A : ℝ) (n d : ℤ) (σ S : ℝ) (v : Vertex) :
    (blockRegion b A n d σ S v).Finite :=
  finite_tilted_rectangle b (blockX n d v) (blockY σ S v) ((A+3)*n) (4*S)

noncomputable def blockVertices (b A : ℝ) (n d : ℤ) (σ S : ℝ) (v : Vertex) : Finset Vertex :=
  (blockRegion_finite b A n d σ S v).toFinset

@[simp] theorem mem_blockVertices (b A : ℝ) (n d : ℤ) (σ S : ℝ) (v p : Vertex) :
    p ∈ blockVertices b A n d σ S v ↔ p ∈ blockRegion b A n d σ S v :=
  (blockRegion_finite b A n d σ S v).mem_toFinset

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GoodSiteTrials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

noncomputable def trialOffset (M : ℕ) (R s : ℝ) (j : Fin M) : ℝ :=
  (2*((j.val : ℝ)+1)-(M : ℝ)-1)*3*trialSpacing R s

noncomputable def trialTranslate (b : ℝ) (X : ℤ) (Y : ℝ)
    (M : ℕ) (R s : ℝ) (j : Fin M) : Vertex :=
  (X,⌊b*X+Y+trialOffset M R s j+1/2⌋)

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GoodSiteEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

noncomputable def siteTrial (μ : Plane → ℝ) (b A R ε s : ℝ) (plus : Bool)
    (n d : ℤ) (M : ℕ) (v : Vertex) (j : Fin M) : Set (Edge → ℝ) :=
  rareFastEvent b (μ (direction b)) (extremeSlope μ b plus) A R ε s n
    (trialTranslate b (blockX n d v) (blockY (contactSign plus) (trialWindow M R s) v) M R s j)

noncomputable def siteConnector (μ : Plane → ℝ) (b R ε s : ℝ) (plus : Bool)
    (n d : ℤ) (M : ℕ) (v : Vertex) (a : ℝ) : Set (Edge → ℝ) :=
  allPairsRegionEvent
    (connectorVertices b (blockX n d v+n) d
      (blockY (contactSign plus) (trialWindow M R s) v) (trialWindow M R s) s)
    (connectorWindow b (blockX n d v+n)
      (blockY (contactSign plus) (trialWindow M R s) v) (trialWindow M R s))
    (connectorWindow b (blockX n d v+n+d)
      (blockY (contactSign plus) (trialWindow M R s) v+contactSign plus*a*trialWindow M R s)
      (trialWindow M R s))
    (sourceSupportCost μ b plus ε s)

noncomputable def goodSiteEvent (μ : Plane → ℝ) (b A R ε s : ℝ) (plus : Bool)
    (n d : ℤ) (M : ℕ) (v : Vertex) : Set (Edge → ℝ) :=
  {w | (∃ j : Fin M, w ∈ siteTrial μ b A R ε s plus n d M v j) ∧
    w ∈ siteConnector μ b R ε s plus n d M v 1 ∧
    w ∈ siteConnector μ b R ε s plus n d M v 2}

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SourceTilt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge Set Filter MeasureTheory
open scoped Topology
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

noncomputable def sourceCrossingK (shape rate : ℝ) (μ : Plane → ℝ) (b : ℝ) : ℝ :=
  100*(1+|extremeSlope μ b false|+|extremeSlope μ b true|+|coordinateAllowance shape rate|)

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ShortCrossingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge Set Filter MeasureTheory
open scoped Topology
noncomputable def sourceEndpoint (b : ℝ) (n : ℤ) : Vertex := (n,⌊b*n⌋)

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CharacteristicLengths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Filter MeasureTheory
open scoped Topology

noncomputable def firstDyadicExponent (p : ℕ → ℝ) (q : ℝ) : ℕ :=
  by
    classical
    exact if h : ∃ j, p j ≤ q then Nat.find h else 0

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (τ : Edge → Ω → ℝ)

noncomputable def sourceDyadicCrossingProbability (shape rate : ℝ) (μ : Plane → ℝ) (b : ℝ) (k j : ℕ) : ℝ :=
  P.real {ω | (fun e => τ e ω) ∈ crossingEvent b (μ (direction b)) (sourceCrossingK shape rate μ b)
    ((2 : ℝ)^k) ((2 : ℤ)^j) 0}

noncomputable def characteristicExponent (shape rate : ℝ) (μ : Plane → ℝ) (b q : ℝ) (k : ℕ) : ℕ :=
  firstDyadicExponent (sourceDyadicCrossingProbability P τ shape rate μ b k) q

noncomputable def characteristicLength (shape rate : ℝ) (μ : Plane → ℝ) (b q : ℝ) (k : ℕ) : ℤ :=
  (2 : ℤ)^(characteristicExponent P τ shape rate μ b q k)

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GridMeshes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer meshes with a final unit interval, and their comparison with
characteristic lengths at record indices. -/
namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge
open Filter Set MeasureTheory
open scoped Topology

def gridMeshExponent (m j : ℕ) : ℕ := m-(4*j+1)
def gridLastLevel (m : ℕ) : ℕ := (m+2)/4
noncomputable def gridMesh (m j : ℕ) : ℤ := (2 : ℤ)^gridMeshExponent m j
noncomputable def gridWidth (k j : ℕ) : ℤ := (2 : ℤ)^(k-j)

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_EndpointMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer endpoint subdivision for Lemma `gr:variable-endpoints`.
Floors use Euclidean division by a positive mesh, including at negative columns. -/
namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge

noncomputable def meshFloor (x d : ℤ) : ℤ := x / d * d

noncomputable def endpointColumn (x : ℤ) (m j : ℕ) : ℤ := meshFloor x (gridMesh m j)

noncomputable def entranceColumn (x : ℤ) (m J : ℕ) : ℤ :=
  endpointColumn x m J-gridMesh m J
noncomputable def exitColumn (x : ℤ) (m J : ℕ) : ℤ := -entranceColumn (-x) m J

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_EndpointGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed transverse targets and whole-extension support errors for
 gr:variable-endpoints. Rounding is charged once, independently of levels. -/
namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge

open Set Finset

noncomputable def endpointVertex (b r : ℝ) (X : ℤ) : Vertex := (X,⌊b*X+r⌋)

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_EndpointTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge
open Filter Finset
open scoped Topology

noncomputable def endpointErrorTerm (j : ℕ) : ℝ := (j : ℝ)^2*(1/2 : ℝ)^j
noncomputable def endpointErrorTail (J : ℕ) : ℝ := ∑' n : ℕ,endpointErrorTerm (n+J)

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_EndpointBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge
open Set Finset

noncomputable def endpointExtensionError (shape rate K : ℝ) (k J : ℕ) : ℝ :=
  16*(Grid.attachmentAllowance shape rate K)*(2 : ℝ)^k*endpointErrorTail J

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GridCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite supersets of grid intervals and transverse bins, with cardinality
bounds independent of the characteristic scale. -/
namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge
open Finset Set

noncomputable def gridIndexRange (x : ℝ) : Finset ℤ :=
  Finset.Icc (-(⌈x⌉₊ : ℤ)) ⌈x⌉₊

noncomputable def gridTestIndices (A R L s l w : ℝ) : Finset (ℤ × ℤ) :=
  gridIndexRange ((A+4)*L/l) ×ˢ gridIndexRange (R*s/w+1)

noncomputable def gridIndexConstant (A R : ℝ) : ℝ :=
  2*(2*(A+4)+3)*(2*R+5)

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GridEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

noncomputable def gridTestsEvent (shape rate b m₀ K A R : ℝ) (k m J : ℕ) : Set (Edge → ℝ) :=
  {weights | ∀ n ∈ Finset.range (gridLastLevel m+1-J),
    ∀ ih ∈ gridTestIndices A R ((2 : ℝ)^m) ((2 : ℝ)^k) (gridMesh m (n+J)) (gridWidth k (n+J)),
      weights ∈ gridBinGood shape rate b m₀ K ((gridMesh m (n+J))*ih.1) ih.2
        (gridWidth k (n+J)) (gridMesh m (n+J)) (n+J)}

noncomputable def gridConnectionsEvent (shape rate b m₀ K A R : ℝ) (k m J : ℕ) : Set (Edge → ℝ) :=
  {weights | (∀ e, 0 ≤ weights e) ∧ weights ∈ gridTestsEvent shape rate b m₀ K A R k m J}

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_EndpointConnection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge
open Set

/-- A localized finite path between fixed-target lattice vertices. -/
def ColumnConnection (w : Edge → ℝ) (b r m₀ E : ℝ) (S : Set Vertex) (X Y : ℤ) : Prop :=
  ∃ ds, endpointVertex b r X+displacement ds=endpointVertex b r Y ∧
    pathCost w (endpointVertex b r X) ds ≤ m₀*((Y-X : ℤ) : ℝ)+E ∧
    PathIn (endpointVertex b r X) ds S

noncomputable def endpointTube (b r H : ℝ) (B T : ℤ) : Set Vertex :=
  {z | B ≤ z.1 ∧ z.1 ≤ T ∧ |transverse b z-r| ≤ H}

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_EndpointExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Whole entrance and exit paths for Lemma `gr:variable-endpoints`. -/
namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge
open Set

noncomputable def endpointBox (b A R : ℝ) (k m : ℕ) : Set Vertex :=
  {z | |(z.1 : ℝ)| ≤ A*(2 : ℝ)^m ∧ |transverse b z| ≤ R*(2 : ℝ)^k}

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_EndpointCoarseGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge
open Set Finset

noncomputable def coarseColumnIndices (A : ℝ) (J : ℕ) : Finset ℤ :=
  gridIndexRange ((A+2)*(2 : ℝ)^(4*J+1))

noncomputable def coarseRegionFactor (A : ℝ) (J : ℕ) : ℝ := (2*A+8)*(2 : ℝ)^(4*J+1)

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_EndpointEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge
open Set Finset MeasureTheory ProbabilityTheory

lemma endpointBox_finite (b A R : ℝ) (k m : ℕ) : (endpointBox b A R k m).Finite := by
  simpa [endpointBox] using finite_tilted_rectangle b 0 0 (A*(2 : ℝ)^m) (R*(2 : ℝ)^k)

noncomputable def endpointBoxVertices (b A R : ℝ) (k m : ℕ) : Finset Vertex :=
  (endpointBox_finite b A R k m).toFinset

noncomputable def arbitraryEndpointEvent (b m₀ a A R ε : ℝ) (k m : ℕ) : Set (Edge → ℝ) :=
  strictLocalizedEvent (endpointBoxVertices b A R k m) (fun _ _ => True)
    (fun _ ds => support b m₀ a (displacement ds)-ε*(2 : ℝ)^k)

noncomputable def coarsePairIndices (A : ℝ) (J : ℕ) : Finset (ℤ×ℤ) :=
  ((coarseColumnIndices A J) ×ˢ (coarseColumnIndices A J)).filter (fun ij => ij.1 < ij.2)

noncomputable def coarsePairEvent (b m₀ a A R ε : ℝ) (k m J : ℕ) (ij : ℤ×ℤ) : Set (Edge → ℝ) :=
  rareFastEvent b m₀ a (coarseRegionFactor A J) (R+1) (ε/2) ((2 : ℝ)^k)
    (gridMesh m J*ij.2-gridMesh m J*ij.1) (endpointVertex b 0 (gridMesh m J*ij.1))

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GridTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.Grid
open Filter Finset Set
open scoped Topology

noncomputable def gridFailureSeries (shape q : ℝ) (j : ℕ) : ℝ :=
  (2 : ℝ)^(5*j)*(Real.exp (-q*(j : ℝ)^2)+2*Real.exp (-(verticalExponent shape)*(j : ℝ)^2))

noncomputable def gridFailureTail (shape C q : ℝ) (J : ℕ) : ℝ :=
  C*(∑' n : ℕ,gridFailureSeries shape q (n+J))

end GammaFPP.Grid

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_PathSubpaths
attribute [-instance] _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set

@[simp] lemma reverseSteps_append (ds es : List Step) :
    reverseSteps (ds++es)=reverseSteps es++reverseSteps ds := by simp [reverseSteps]

@[simp] lemma reverseSteps_reverse (ds : List Step) : reverseSteps (reverseSteps ds)=ds := by
  have hr (d : Step) : d.reverse.reverse=d := by cases d <;> rfl
  simp [reverseSteps,List.map_map,Function.comp_def,hr]

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SpatialWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set Finset MeasureTheory ProbabilityTheory

noncomputable def translatedArbitraryEndpointEvent (b m₀ a A R ε : ℝ) (k m : ℕ)
    (t : Vertex) : Set (Edge → ℝ) :=
  {w | (fun e => w (shiftEdge t e)) ∈ arbitraryEndpointEvent b m₀ a A R ε k m}

noncomputable def eitherEndpointEvent (b m₀ am ap A R ε : ℝ) (k m : ℕ) (t : Vertex) : Set (Edge → ℝ) :=
  translatedArbitraryEndpointEvent b m₀ am A R ε k m t ∪
    translatedArbitraryEndpointEvent b m₀ ap A R ε k m t

noncomputable def spatialTranslate (b : ℝ) (k m : ℕ) (ih : ℤ×ℤ) : Vertex :=
  (ih.1*(2 : ℤ)^m,⌊b*(ih.1*(2 : ℤ)^m)⌋+ih.2*(2 : ℤ)^k)

noncomputable def spatialRareEvent (b m₀ am ap K η : ℝ) (k m : ℕ) (ih : ℤ×ℤ) : Set (Edge → ℝ) :=
  eitherEndpointEvent b m₀ am ap 4 4 η k m (spatialTranslate b k m ih) ∪
    crossingEvent b m₀ K ((2 : ℝ)^k) ((2 : ℤ)^m) (spatialTranslate b k m (ih+(1,0)))

/-- Exact labelled path witnesses for the two defining spatial rare events.
A support-defect witness retains which strict bound it satisfies. -/
noncomputable def spatialWitnessFamily (b m₀ am ap K η : ℝ) (k m : ℕ) (ih : ℤ×ℤ) : Set GammaFPP.BK.StrictPathWitness :=
  {p | (PathIn p.start p.steps {z | z-spatialTranslate b k m ih ∈ endpointBox b 4 4 k m} ∧
      (p.bound=support b m₀ am (displacement p.steps)-η*(2 : ℝ)^k ∨
       p.bound=support b m₀ ap (displacement p.steps)-η*(2 : ℝ)^k)) ∨
    (p.start.1=(spatialTranslate b k m (ih+(1,0))).1 ∧
      (p.start+displacement p.steps).1=(spatialTranslate b k m (ih+(1,0))).1+(2 : ℤ)^m ∧
      PathIn p.start p.steps (rareFastRegion b 1 8 ((2 : ℝ)^k) ((2 : ℤ)^m) (spatialTranslate b k m (ih+(1,0)))) ∧
      p.bound=m₀*(2 : ℤ)^m+K*(2 : ℝ)^k)}

lemma translatedEndpointBox_finite (b A R : ℝ) (k m : ℕ) (t : Vertex) :
    {z | z-t ∈ endpointBox b A R k m}.Finite := by
  apply ((endpointBox_finite b A R k m).image (fun p => t+p)).subset
  intro z hz
  exact ⟨z-t,hz,by abel_nf⟩

noncomputable def spatialWitnessVertices (b : ℝ) (k m : ℕ) (ih : ℤ×ℤ) : Finset Vertex :=
  (translatedEndpointBox_finite b 4 4 k m (spatialTranslate b k m ih)).toFinset ∪
    rareFastVertices b 1 8 ((2 : ℝ)^k) ((2 : ℤ)^m) (spatialTranslate b k m (ih+(1,0)))

noncomputable def spatialWitnessSupport (b : ℝ) (k m : ℕ) (ih : ℤ×ℤ) : Finset Edge :=
  internalEdges (spatialWitnessVertices b k m ih)

noncomputable def spatialListSupport (b : ℝ) (k m : ℕ) (is : List (ℤ×ℤ)) : Finset Edge :=
  is.toFinset.biUnion (spatialWitnessSupport b k m)

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SpatialChunkGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set

noncomputable def spatialChunkIndex (b : ℝ) (k m : ℕ) (p : Vertex) : ℤ×ℤ :=
  (p.1/(2 : ℤ)^m,⌊transverse b p/(2 : ℝ)^k⌋)

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SpatialFirstExit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set

noncomputable def chunkInterior (b : ℝ) (k m : ℕ) (v : Vertex) : Prop :=
  |v.1| < 2*(2 : ℤ)^m ∧ |transverse b v| < (2 : ℝ)^k

noncomputable def FullSpatialChunk (b : ℝ) (k m : ℕ) (ds : List Step) : Prop :=
  (∀ i < ds.length, chunkInterior b k m (displacement (ds.take i))) ∧
    ¬chunkInterior b k m (displacement ds)

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SpatialChunks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set

noncomputable def chunkIndexTail (b : ℝ) (k m : ℕ) : Vertex → List (List Step) → List (ℤ×ℤ)
  | _,[] => []
  | p,q::qs => spatialChunkIndex b k m (p+displacement q)::chunkIndexTail b k m (p+displacement q) qs

def BoundedIndexSteps : (ℤ×ℤ) → List (ℤ×ℤ) → Prop
  | _,[] => True
  | p,q::qs => |q.1-p.1| ≤ 3 ∧ |q.2-p.2| ≤ 3 ∧ BoundedIndexSteps q qs

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_WitnessSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP
open Set

/-- Preserve every chunk position while truncating the concatenated witness list. -/
def takeWitnessPacks {α : Type*} : ℕ → List (List α) → List (List α)
  | _,[] => []
  | t,ws::packs => ws.take t :: takeWitnessPacks (t-ws.length) packs

/-- A list of event labels determined only by the ordered chunk indices
and by the number of selected witnesses in each position. -/
def witnessLabels : List ℕ → List (ℤ×ℤ) → List (ℤ×ℤ)
  | [],_ => []
  | _,[] => []
  | n::ns,i::is => List.replicate n i ++ witnessLabels ns is

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_WitnessEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP
open Finset

noncomputable def spatialNeighbors (i : ℤ×ℤ) : Finset (ℤ×ℤ) :=
  ((Icc (-3 : ℤ) 3) ×ˢ (Icc (-3 : ℤ) 3)).image (fun d => i+d)

noncomputable def spatialItineraries (i : ℤ×ℤ) : ℕ → Finset (List (ℤ×ℤ))
  | 0 => {[]}
  | n+1 => (spatialNeighbors i).biUnion (fun j => (spatialItineraries j n).image (List.cons j))

def increaseFirst : List ℕ → List ℕ
  | [] => []
  | n::ns => (n+1)::ns

/-- Pascal recursion gives a finite cover of all weak compositions. -/
noncomputable def compositionCandidates : ℕ → ℕ → Finset (List ℕ)
  | 0,t => {[t]}
  | n+1,0 => {List.replicate (n+2) 0}
  | n+1,t+1 => (compositionCandidates n (t+1)).image (List.cons 0) ∪
      (compositionCandidates (n+1) t).image increaseFirst
termination_by n t => n+t

noncomputable def compositionCover (n t : ℕ) : Finset (List ℕ) :=
  (compositionCandidates n t).filter (fun ns => ns.length=n+1 ∧ ns.sum=t)

end GammaFPP.CrossingBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SpatialBadPathCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP
open Set Finset

/-- The manuscript's bad simple-path event at a fixed scale. The path starts
at the origin; the exact first-exit conditions and empty remainder are kept. -/
def SpatialBadPath (w : Edge → ℝ) (b m₀ a η : ℝ) (k m N : ℕ) : Prop :=
  ∃ blocks : List (List Step), ∃ rest : List Step,
    blocks.length=N ∧ (∀ q ∈ blocks, FullSpatialChunk b k m q) ∧
    (∀ i ≤ rest.length, chunkInterior b k m (displacement (rest.take i))) ∧
    ((trace 0 (blocks.flatten++rest)).map traversalEdge).Nodup ∧
    defect w b m₀ a 0 (blocks.flatten++rest) < N*η*(2 : ℝ)^k/2

end GammaFPP.CrossingBridge

end OAI
end


