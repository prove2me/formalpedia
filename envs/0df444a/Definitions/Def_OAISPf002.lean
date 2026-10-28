-- Prove2me | Definitions.Def_OAISPf002
-- name    : OAISPf002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T10:39:10.277153+00:00
-- url     : https://prove2.me/theorems/61cdedd8-9da0-45ef-8322-d033ff3ef8c3
-- title:
--   Definitions bundle OAISPf002 of the split of OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PlanarFPP.manuscriptMain`, carved from OpenAI's openai/math development (OpenAI, *Strict convexity and differentiability of the planar exponential first-passage limit shape*, OpenAI Math Release, September 24, 2026, result family 212, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 161 declarations of OpenAI's Lean: 119 definitions, 2 inductive types or structures, 4 instances and 36 theorems. The definitions and types are `OAI.PlanarFPP.ColumnConnection`, `OAI.PlanarFPP.DependsOnEdges`, `OAI.PlanarFPP.DyadicPathGood`, `OAI.PlanarFPP.EnclosingLoop`, `OAI.PlanarFPP.FullSpatialChunk`, `OAI.PlanarFPP.GoodOrigin`, `OAI.PlanarFPP.RoundedDisjointPaths`, `OAI.PlanarFPP.RoundedPathGood`, `OAI.PlanarFPP.SeparatedGoodIndependent`, `OAI.PlanarFPP.SpatialBadPath`, `OAI.PlanarFPP.SquareLoop`, `OAI.PlanarFPP.SquareLoop.NoRepeatedSides`, `OAI.PlanarFPP.SquareLoop.badSites`, `OAI.PlanarFPP.SquareLoop.upLeftIndices`, `OAI.PlanarFPP.SquareLoop.winding`, `OAI.PlanarFPP.SquareSide.aboveAxis`, `OAI.PlanarFPP.SquareSide.axisCross`, `OAI.PlanarFPP.SquareSide.head`, `OAI.PlanarFPP.SquareSide.opposite`, `OAI.PlanarFPP.SquareSide.rayCross`, `OAI.PlanarFPP.SquareSide.tail`, `OAI.PlanarFPP.Step.corner`, `OAI.PlanarFPP.Step.left`, `OAI.PlanarFPP.StrictDisjointPaths`, `OAI.PlanarFPP.StrictPathEvent`, `OAI.PlanarFPP.StrictPathWitness`, `OAI.PlanarFPP.StrictPathWitness.Good`, `OAI.PlanarFPP.StrictPathWitness.bits`, `OAI.PlanarFPP.StrictPathWitness.edges`, `OAI.PlanarFPP.UniformShape`, `OAI.PlanarFPP.actualSourceTimeConstant`, `OAI.PlanarFPP.allPairsRegionEvent`, `OAI.PlanarFPP.arbitraryEndpointEvent`, `OAI.PlanarFPP.badConnections`, `OAI.PlanarFPP.badContourEvent`, `OAI.PlanarFPP.boundaryNext`, `OAI.PlanarFPP.boundaryPerm`, `OAI.PlanarFPP.boundaryPrev`, `OAI.PlanarFPP.boundarySuccessor`, `OAI.PlanarFPP.boundedLocalizedEvent` and 81 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `FirstPassage_ActualTimeConstant`, `FirstPassage_BKBinaryRanks`, `FirstPassage_BKBitLaw`, `FirstPassage_BKContinuous`, `FirstPassage_BKDyadicPaths`, `FirstPassage_BKQuantization`, `FirstPassage_BoundaryGeometry`, `FirstPassage_BoundaryWinding`, `FirstPassage_CharacteristicLengths`, `FirstPassage_CompanionModel`, `FirstPassage_ConnectorEvents`, `FirstPassage_ConnectorGeometry`, `FirstPassage_ConnectorProbability`, `FirstPassage_ContourEnumeration`, `FirstPassage_ContourLocalization`, `FirstPassage_CoordinateTails`, `FirstPassage_CrossingChain`, `FirstPassage_CrossingTilt`, `FirstPassage_CrossingTrialGeometry`, `FirstPassage_EndpointConnection`, `FirstPassage_EndpointEvents`, `FirstPassage_EndpointExtensions`, `FirstPassage_EndpointGeometry`, `FirstPassage_EndpointTranslation`, `FirstPassage_FiniteEdgeEvents`, `FirstPassage_FiniteEdgeTilt`, `FirstPassage_GoodSiteEvents`, `FirstPassage_GridConnectionGeometry`, `FirstPassage_GridConnections`, `FirstPassage_GridProbability`, `FirstPassage_GridTrials`, `FirstPassage_HighDensityOriented`, `FirstPassage_LatticeSwap`, `FirstPassage_LocalizedEvents`, `FirstPassage_OrientedCompactness`, `FirstPassage_OrientedProbability`, `FirstPassage_PassageTime`, `FirstPassage_PathSubpaths`, `FirstPassage_PathWitnesses`, `FirstPassage_Paths`, `FirstPassage_ProbabilityFoundations`, `FirstPassage_RareFastEvents`, `FirstPassage_RealScaleConnections`, `FirstPassage_SeparatedSelection`, `FirstPassage_ShapeProbability`, `FirstPassage_ShortCrossingGeometry`, `FirstPassage_SourceTilt`, `FirstPassage_SpatialBadPathCover`, `FirstPassage_SpatialChunkGeometry`, `FirstPassage_SpatialChunks`, `FirstPassage_SpatialFirstExit`, `FirstPassage_SpatialModulus`, `FirstPassage_SpatialRareEvents`, `FirstPassage_SpatialWitnesses`, `FirstPassage_SphereCharts`, `FirstPassage_SquareLoops`, `FirstPassage_TiltRegionCount`, `FirstPassage_Translation`, `FirstPassage_UniformShape`, `FirstPassage_VerticalIntervals`.
--
--   **Imports.** It imports the published bundle `Def_PlanarFirstPassage`; the bundles `OAISPf000` and `OAISPf001` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.PlanarFPP.actualSourceTimeConstant_lattice_limits`, `OAI.PlanarFPP.actual_differentiable_horizontal`, `OAI.PlanarFPP.actual_grid_trial_probabilities`, `OAI.PlanarFPP.actual_spatial_rare_scales`, `OAI.PlanarFPP.ae_eventually_spatial_long_paths`, `OAI.PlanarFPP.exponential_arbitraryEndpoint_tendsto_of_grids`, `OAI.PlanarFPP.exponential_characteristic_lengths_exist`, `OAI.PlanarFPP.exponential_characteristic_lengths_ratio`, `OAI.PlanarFPP.exponential_coarsePair_bound`, `OAI.PlanarFPP.exponential_goodSite_path_probability_zero` and `OAI.PlanarFPP.exponential_source_connector_test`; the proofs of `OAI.PlanarFPP.actualSourceTimeConstant_lattice_limits`, `OAI.PlanarFPP.actual_differentiable_horizontal`, `OAI.PlanarFPP.actual_grid_trial_probabilities`, `OAI.PlanarFPP.actual_spatial_rare_scales`, `OAI.PlanarFPP.ae_eventually_spatial_long_paths`, `OAI.PlanarFPP.exponential_arbitraryEndpoint_tendsto_of_grids`, `OAI.PlanarFPP.exponential_characteristic_lengths_exist`, `OAI.PlanarFPP.exponential_characteristic_lengths_ratio`, `OAI.PlanarFPP.exponential_coarsePair_bound`, `OAI.PlanarFPP.exponential_goodSite_path_probability_zero`, `OAI.PlanarFPP.exponential_source_connector_test` and `OAI.PlanarFPP.manuscriptMain`.
-- source:
--   OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 212; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFirstPassage
import Definitions.Def_OAISPf000
import Definitions.Def_OAISPf001

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_Paths
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instFintypeStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

noncomputable def defect (τ : Edge → ℝ) (b m a : ℝ) (p : Vertex) (ds : List Step) : ℝ :=
  pathCost τ p ds - support b m a (displacement ds)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_PassageTime
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instFintypeStep _root_.OAI.PlanarFPP.rateOneProbability
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

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ProbabilityFoundations
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instFintypeStep
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

noncomputable def exponentialProductLaw : Measure (Edge → ℝ) :=
  Measure.infinitePi (fun _ : Edge => expMeasure 1)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_Translation
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set

def shiftEdge (a : Vertex) (e : Edge) : Edge := (a+e.1,e.2)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_CompanionModel
attribute [-instance] _root_.OAI.CompanionFPP.countable_lattice_walk _root_.OAI.CompanionFPP.encodable_lattice_walk _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set

lemma companion_adj_step (p : Vertex) (d : Step) :
    CompanionFPP.lattice.Adj p (p+d.delta) := by
  cases d <;> simp [CompanionFPP.lattice, Step.delta]

lemma companion_adj_iff (p q : Vertex) :
    CompanionFPP.lattice.Adj p q ↔ ∃ d : Step, q=p+d.delta := by
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

def companionEdge (e : Edge) : CompanionFPP.Edge :=
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

noncomputable def companionEdgeEquiv : Edge ≃ CompanionFPP.Edge :=
  Equiv.ofBijective companionEdge ⟨companionEdge_injective,companionEdge_surjective⟩

noncomputable def companionWeights (w : Edge → ℝ) : CompanionFPP.Environment :=
  fun e => w (companionEdgeEquiv.symm e)

@[simp] lemma companionWeights_edge (w : Edge → ℝ) (e : Edge) :
    companionWeights w (companionEdge e)=w e := by
  change w (companionEdgeEquiv.symm (companionEdgeEquiv e))=w e
  rw [companionEdgeEquiv.symm_apply_apply]

@[simp] lemma companion_pathCost_copy (w : CompanionFPP.Environment)
    {p q p' q' : Vertex} (walk : CompanionFPP.lattice.Walk p q) (hp : p=p') (hq : q=q') :
    CompanionFPP.pathCost w (walk.copy hp hq) = CompanionFPP.pathCost w walk := by
  subst p'; subst q'; rfl

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_CoordinateTails
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instFintypeStep
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

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SpatialModulus
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Finset Filter Set
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

def badConnections (τ : Edge → Ω → ℝ) (ε : ℝ) (n : ℕ) : Set Ω :=
  ⋃ pq ∈ (latticeBox n) ×ˢ (latticeBox n),
    {ω | 4 * (latticeDistance pq.1 pq.2 : ℝ) + ε * n ≤
      pathCost (fun e => τ e ω) pq.1 (coordinatePath pq.1 pq.2)}

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_UniformShape
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

noncomputable def rescaledPassage (w : Edge → ℝ) (n : ℕ) (v : Plane) : ℝ :=
  passageTime w 0 (latticeFloor ((n : ℝ) • v)) / n

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

def UniformShape (w : Edge → ℝ) (μ : Plane → ℝ) : Prop :=
  ∀ ε > 0, ∃ R : ℝ, 0 < R ∧ ∀ z : Vertex, R ≤ ‖latticeEmbed z‖ →
    |passageTime w 0 z-μ (latticeEmbed z)| ≤ ε * ‖latticeEmbed z‖

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_RealScaleConnections
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory Filter Set
open scoped Topology

noncomputable def scaledLatticePoint (t : ℝ) (p : Vertex) : Plane :=
  (1/t) • latticeEmbed p

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ActualTimeConstant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

noncomputable def actualSourceTimeConstant (v : Plane) : ℝ :=
  CompanionFPP.timeSeminorm (v 0,v 1)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_FiniteEdgeEvents
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set Finset

def DependsOnEdges (A : Set (Edge → ℝ)) (S : Finset Edge) : Prop :=
  ∀ w w', (∀ e ∈ S, w e=w' e) → (w ∈ A ↔ w' ∈ A)

noncomputable def extendEdgeWeights (S : Finset Edge) (w : S → ℝ) : Edge → ℝ :=
  fun e => if he : e ∈ S then w ⟨e,he⟩ else 0

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_LocalizedEvents
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

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

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BKDyadicPaths
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset

structure StrictPathWitness where
  start : Vertex
  steps : List Step
  bound : ℝ

namespace StrictPathWitness

def edges (p : StrictPathWitness) : Finset Edge := pathEdges p.start p.steps

def bits (p : StrictPathWitness) (t : ℕ) : Finset (Edge × Fin t) := p.edges ×ˢ univ

end StrictPathWitness

noncomputable def dyadicSurvival (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) : ℝ :=
  ∑ h : Fin t, if (e,h) ∈ x then 1/(2:ℝ)^(h.val+1) else 0

def DyadicPathGood (t : ℕ) (x : Finset (Edge × Fin t)) (p : StrictPathWitness) : Prop :=
  (∀ e ∈ p.edges, 0 < dyadicSurvival t x e) ∧
    pathCost (fun e => -Real.log (dyadicSurvival t x e)) p.start p.steps < p.bound

noncomputable def dyadicPathFamily (S : Finset Edge) (t : ℕ) (F : Set StrictPathWitness) :
    Finset (Finset (Edge × Fin t)) := by
  classical
  exact (S ×ˢ (univ : Finset (Fin t))).powerset.filter
    (fun x => ∃ p ∈ F, p.edges ⊆ S ∧ DyadicPathGood t x p)

noncomputable def dyadicDisjointPathFamily (S : Finset Edge) (t : ℕ)
    (Fs : List (Set StrictPathWitness)) : Finset (Finset (Edge × Fin t)) := by
  classical
  exact (S ×ˢ (univ : Finset (Fin t))).powerset.filter (fun x =>
    ∃ ps : List StrictPathWitness,
      List.Forall₂ (fun p F => p ∈ F ∧ p.edges ⊆ S ∧ DyadicPathGood t x p) ps Fs ∧
      ps.Pairwise (fun p q => Disjoint p.edges q.edges))

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BKBinaryRanks
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset

noncomputable def dyadicPositions (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) : Finset ℕ :=
  ((univ : Finset (Fin t)).filter (fun h => (e,h) ∈ x)).image (fun h => t-(h.val+1))

noncomputable def dyadicRank (t : ℕ) (x : Finset (Edge × Fin t)) (e : Edge) : ℕ :=
  ∑ a ∈ dyadicPositions t x e, 2^a

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BKQuantization
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Filter
open scoped Topology

def RoundedPathGood (t : ℕ) (w : Edge → ℝ) (p : StrictPathWitness) : Prop :=
  (∀ e ∈ p.edges, 0 < roundedSurvival t (w e)) ∧
    pathCost (fun e => roundedEdgeCost t (w e)) p.start p.steps < p.bound

def StrictPathWitness.Good (w : Edge → ℝ) (p : StrictPathWitness) : Prop :=
  pathCost w p.start p.steps < p.bound

def StrictDisjointPaths (S : Finset Edge) (Fs : List (Set StrictPathWitness)) (w : Edge → ℝ) : Prop :=
  ∃ ps : List StrictPathWitness,
    List.Forall₂ (fun p F => p ∈ F ∧ p.edges ⊆ S ∧ p.Good w) ps Fs ∧
    ps.Pairwise (fun p q => Disjoint p.edges q.edges)

def RoundedDisjointPaths (S : Finset Edge) (Fs : List (Set StrictPathWitness))
    (t : ℕ) (w : Edge → ℝ) : Prop :=
  ∃ ps : List StrictPathWitness,
    List.Forall₂ (fun p F => p ∈ F ∧ p.edges ⊆ S ∧ RoundedPathGood t w p) ps Fs ∧
    ps.Pairwise (fun p q => Disjoint p.edges q.edges)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BKBitLaw
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

def dyadicRankCell (τ : Edge → Ω → ℝ) (S : Finset Edge) (t : ℕ)
    (x : Finset (Edge × Fin t)) : Set Ω :=
  {ω | ∀ e ∈ S, ⌊(2:ℝ)^t*Real.exp (-τ e ω)⌋₊ = dyadicRank t x e}

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BKContinuous
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal

def StrictPathEvent (S : Finset Edge) (F : Set StrictPathWitness) (w : Edge → ℝ) : Prop :=
  ∃ p ∈ F, p.edges ⊆ S ∧ p.Good w

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BoundaryGeometry
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset

def Step.left : Step → Step
  | .east => .north | .north => .west | .west => .south | .south => .east

def Step.corner : Step → Vertex
  | .east => (0,0) | .north => (1,0) | .west => (1,1) | .south => (0,1)

def SquareSide.tail (e : SquareSide) : Vertex := e.1 + e.2.corner

def SquareSide.head (e : SquareSide) : Vertex := e.tail + e.2.delta

instance instDecidableIsBoundarySide (S : Finset Vertex) (e : SquareSide) : Decidable (IsBoundarySide S e) :=
  inferInstanceAs (Decidable (_ ∧ _))

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

noncomputable def boundaryPerm (S : Finset Vertex) : Equiv.Perm (BoundarySide S) :=
  Equiv.ofBijective (boundarySuccessor S)
    ⟨boundarySuccessor_injective S, Finite.surjective_of_injective
      (boundarySuccessor_injective S)⟩

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BoundaryWinding
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.rateOneProbability
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
-- module Solutions.OAIS_PlanarFPP.FirstPassage_FiniteEdgeTilt
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

noncomputable def scaleFiniteEdges (S : Finset Edge) (α : ℝ) (w : Edge → ℝ) : Edge → ℝ :=
  fun e => if e ∈ S then α*w e else w e

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SquareLoops
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ContourLocalization
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

theorem rayCross_ne_zero_location (e : SquareSide) (he : e.rayCross ≠ 0) :
    0 < e.tail.1 ∧ 0 ≤ e.tail.2 ∧ e.tail.2 ≤ 1 := by
  rcases e with ⟨⟨x,y⟩,d⟩
  cases d <;> simp_all [rayCross, tail, Step.corner]

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

theorem start_mem_box (c : SquareLoop m) (hm : 0 < m) (hc : c.winding ≠ 0) :
    (c.side ⟨0,hm⟩).tail ∈ latticeBox (m+1) := by
  obtain ⟨⟨i,hi⟩,⟨j,hj0,hj1,hj2⟩⟩ := c.winding_locations hc
  have hbi := c.tail_bounds hm i
  have hbj := c.tail_bounds hm j
  have hi' := i.isLt
  have hj' := j.isLt
  simp only [latticeBox, mem_product, mem_Icc]
  constructor <;> constructor <;> omega

end SquareLoop

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ContourEnumeration
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

abbrev EnclosingLoop (n : ℕ) :=
  {c : SquareLoop (n+1) // c.winding ≠ 0 ∧ c.NoRepeatedSides}

def enclosingLoopCode (n : ℕ) (c : EnclosingLoop n) :
    {p // p ∈ latticeBox (n+2)} × (Fin (n+1) → Step) :=
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
-- module Solutions.OAIS_PlanarFPP.FirstPassage_OrientedCompactness
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory

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

def orientedReachable (G : Vertex → Prop) (p : Vertex) : Set Vertex :=
  ⋃ n : ℕ, (orientedEndpoints G p n : Set Vertex)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SeparatedSelection
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset Set

def latticeNear (k : ℕ) (p q : Vertex) : Prop :=
  (q.1-p.1).natAbs ≤ k ∧ (q.2-p.2).natAbs ≤ k

instance instDecidableLatticeNear (k : ℕ) (p q : Vertex) : Decidable (latticeNear k p q) :=
  inferInstanceAs (Decidable (_ ∧ _))

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_OrientedProbability
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
-- module Solutions.OAIS_PlanarFPP.FirstPassage_HighDensityOriented
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ShapeProbability
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

def GoodOrigin (μ : Plane → ℝ) (α : ℝ) (C : ℕ) (η δ : ℝ) (n : ℕ)
    (w : Edge → ℝ) : Prop :=
  (∀ e, 0 ≤ w e) ∧
  (∀ z : Vertex, ‖latticeEmbed z‖ ≤ (C : ℝ)*n →
    |passageTime w 0 z-μ (latticeEmbed z)| ≤ η*n) ∧
  (∀ z : Vertex, δ*n/3 ≤ ‖latticeEmbed z‖ → α*δ*n/6 ≤ passageTime w 0 z)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_CrossingChain
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Filter
open scoped Topology

def crossingChain (initialPath : List Step) (trial connector : ℕ → List Step) : ℕ → List Step
  | 0 => initialPath ++ trial 0
  | n+1 => crossingChain initialPath trial connector n ++ (connector n ++ trial (n+1))

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ConnectorEvents
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set MeasureTheory Filter
open scoped Topology

def allPairsRegionEvent (V : Finset Vertex) (I J : Set Vertex)
    (bound : Vertex → Vertex → ℝ) : Set (Edge → ℝ) :=
  {w | ∀ p ∈ I, ∀ q ∈ J, w ∈ boundedLocalizedEvent V
    (fun a ds => a=p ∧ a+displacement ds=q) (fun _ _ => bound p q)}

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_CrossingTrialGeometry
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset

noncomputable def trialTranslate (b : ℝ) (X : ℤ) (Y : ℝ)
    (M : ℕ) (R s : ℝ) (j : Fin M) : Vertex :=
  (X,⌊b*X+Y+trialOffset M R s j+1/2⌋)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ConnectorGeometry
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

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

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ConnectorProbability
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology

noncomputable def sourceSupportCost (μ : Plane → ℝ) (b : ℝ) (plus : Bool)
    (ε s : ℝ) (p q : Vertex) : ℝ :=
  μ (direction b)*xCoord (latticeEmbed (q-p))+
    extremeSlope μ b plus*rCoord b (latticeEmbed (q-p))+ε*s/2

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_RareFastEvents
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

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

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GoodSiteEvents
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory Filter
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

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_TiltRegionCount
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset

noncomputable def tiltColumn (b s : ℝ) (x : ℤ) : Finset Vertex :=
  {x} ×ˢ Finset.Icc ⌈b*x-8*s⌉ ⌊b*x+8*s⌋

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_CrossingTilt
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

noncomputable def crossingEvent (b m K s : ℝ) (n : ℤ) (t : Vertex) : Set (Edge → ℝ) :=
  strictLocalizedEvent (rareFastVertices b 1 8 s n t)
    (fun p ds => p.1=t.1 ∧ (p+displacement ds).1=t.1+n)
    (fun _ _ => m*n+K*s)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SourceTilt
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

noncomputable def sourceCrossingK (μ : Plane → ℝ) (b : ℝ) : ℝ :=
  100*(1+|extremeSlope μ b false|+|extremeSlope μ b true|)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_ShortCrossingGeometry
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

noncomputable def sourceEndpoint (b : ℝ) (n : ℤ) : Vertex := (n,⌊b*n⌋)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_CharacteristicLengths
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (τ : Edge → Ω → ℝ)

noncomputable def sourceDyadicCrossingProbability (μ : Plane → ℝ) (b : ℝ) (k j : ℕ) : ℝ :=
  P.real {ω | (fun e => τ e ω) ∈ crossingEvent b (μ (direction b)) (sourceCrossingK μ b)
    ((2 : ℝ)^k) ((2 : ℤ)^j) 0}

noncomputable def characteristicExponent (μ : Plane → ℝ) (b q : ℝ) (k : ℕ) : ℕ :=
  firstDyadicExponent (sourceDyadicCrossingProbability P τ μ b k) q

noncomputable def characteristicLength (μ : Plane → ℝ) (b q : ℝ) (k : ℕ) : ℤ :=
  (2 : ℤ)^(characteristicExponent P τ μ b q k)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointGeometry
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

noncomputable def endpointVertex (b r : ℝ) (X : ℤ) : Vertex := (X,⌊b*X+r⌋)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridTrials
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

noncomputable def gridTrialTranslate (b : ℝ) (X h w : ℤ) (t : ℕ) : Vertex :=
  (X,⌊b*X⌋+(h+30*(t+1 : ℕ))*w)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_VerticalIntervals
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def verticalIntervalEdges (X lo hi : ℤ) : Finset Edge :=
  (Finset.Ico lo hi).image (fun y => ((X,y),true))

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridConnectionGeometry
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

noncomputable def transverseIntervalEdges (b : ℝ) (X : ℤ) (lo hi : ℝ) : Finset Edge :=
  verticalIntervalEdges X ⌈lo+b*X⌉ ⌊hi+b*X⌋

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridProbability
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

noncomputable def gridBinGood (b m K : ℝ) (X h w l : ℤ) (j : ℕ) : Set (Edge → ℝ) :=
  {weights | (∃ t : Fin (j^2), weights ∈ crossingEvent b m K w l (gridTrialTranslate b X h w t)) ∧
    (∑ e ∈ transverseIntervalEdges b X (gridIntervalLower h w) (gridIntervalUpper j h w),weights e)
      ≤ 100*(j : ℝ)^2*w ∧
    (∑ e ∈ transverseIntervalEdges b (X+l) (gridIntervalLower h w) (gridIntervalUpper j h w),weights e)
      ≤ 100*(j : ℝ)^2*w}

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridConnections
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

noncomputable def gridTestsEvent (b m₀ K A R : ℝ) (k m J : ℕ) : Set (Edge → ℝ) :=
  {weights | ∀ n ∈ Finset.range (gridLastLevel m+1-J),
    ∀ ih ∈ gridTestIndices A R ((2 : ℝ)^m) ((2 : ℝ)^k) (gridMesh m (n+J)) (gridWidth k (n+J)),
      weights ∈ gridBinGood b m₀ K ((gridMesh m (n+J))*ih.1) ih.2
        (gridWidth k (n+J)) (gridMesh m (n+J)) (n+J)}

noncomputable def gridConnectionsEvent (b m₀ K A R : ℝ) (k m J : ℕ) : Set (Edge → ℝ) :=
  {weights | (∀ e, 0 ≤ weights e) ∧ weights ∈ gridTestsEvent b m₀ K A R k m J}

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointConnection
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

def ColumnConnection (w : Edge → ℝ) (b r m₀ E : ℝ) (S : Set Vertex) (X Y : ℤ) : Prop :=
  ∃ ds, endpointVertex b r X+displacement ds=endpointVertex b r Y ∧
    pathCost w (endpointVertex b r X) ds ≤ m₀*((Y-X : ℤ) : ℝ)+E ∧
    PathIn (endpointVertex b r X) ds S

noncomputable def endpointTube (b r H : ℝ) (B T : ℤ) : Set Vertex :=
  {z | B ≤ z.1 ∧ z.1 ≤ T ∧ |transverse b z-r| ≤ H}

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointExtensions
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

noncomputable def endpointBox (b A R : ℝ) (k m : ℕ) : Set Vertex :=
  {z | |(z.1 : ℝ)| ≤ A*(2 : ℝ)^m ∧ |transverse b z| ≤ R*(2 : ℝ)^k}

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointEvents
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

lemma endpointBox_finite (b A R : ℝ) (k m : ℕ) : (endpointBox b A R k m).Finite := by
  simpa [endpointBox] using finite_tilted_rectangle b 0 0 (A*(2 : ℝ)^m) (R*(2 : ℝ)^k)

noncomputable def endpointBoxVertices (b A R : ℝ) (k m : ℕ) : Finset Vertex :=
  (endpointBox_finite b A R k m).toFinset

noncomputable def arbitraryEndpointEvent (b m₀ a A R ε : ℝ) (k m : ℕ) : Set (Edge → ℝ) :=
  strictLocalizedEvent (endpointBoxVertices b A R k m) (fun _ _ => True)
    (fun _ ds => support b m₀ a (displacement ds)-ε*(2 : ℝ)^k)

noncomputable def coarsePairEvent (b m₀ a A R ε : ℝ) (k m J : ℕ) (ij : ℤ×ℤ) : Set (Edge → ℝ) :=
  rareFastEvent b m₀ a (coarseRegionFactor A J) (R+1) (ε/2) ((2 : ℝ)^k)
    (gridMesh m J*ij.2-gridMesh m J*ij.1) (endpointVertex b 0 (gridMesh m J*ij.1))

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_EndpointTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable def translatedArbitraryEndpointEvent (b m₀ a A R ε : ℝ) (k m : ℕ)
    (t : Vertex) : Set (Edge → ℝ) :=
  {w | (fun e => w (shiftEdge t e)) ∈ arbitraryEndpointEvent b m₀ a A R ε k m}

noncomputable def eitherEndpointEvent (b m₀ am ap A R ε : ℝ) (k m : ℕ) (t : Vertex) : Set (Edge → ℝ) :=
  translatedArbitraryEndpointEvent b m₀ am A R ε k m t ∪
    translatedArbitraryEndpointEvent b m₀ ap A R ε k m t

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_PathSubpaths
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

@[simp] lemma reverseSteps_append (ds es : List Step) :
    reverseSteps (ds++es)=reverseSteps es++reverseSteps ds := by simp [reverseSteps]

@[simp] lemma reverseSteps_reverse (ds : List Step) : reverseSteps (reverseSteps ds)=ds := by
  have hr (d : Step) : d.reverse.reverse=d := by cases d <;> rfl
  simp [reverseSteps,List.map_map,Function.comp_def,hr]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_PathWitnesses
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

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
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SpatialRareEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable def spatialTranslate (b : ℝ) (k m : ℕ) (ih : ℤ×ℤ) : Vertex :=
  (ih.1*(2 : ℤ)^m,⌊b*(ih.1*(2 : ℤ)^m)⌋+ih.2*(2 : ℤ)^k)

noncomputable def spatialRareEvent (b m₀ am ap K η : ℝ) (k m : ℕ) (ih : ℤ×ℤ) : Set (Edge → ℝ) :=
  eitherEndpointEvent b m₀ am ap 4 4 η k m (spatialTranslate b k m ih) ∪
    crossingEvent b m₀ K ((2 : ℝ)^k) ((2 : ℤ)^m) (spatialTranslate b k m (ih+(1,0)))

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SpatialWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

noncomputable def spatialWitnessFamily (b m₀ am ap K η : ℝ) (k m : ℕ) (ih : ℤ×ℤ) : Set StrictPathWitness :=
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

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SpatialChunkGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

noncomputable def spatialChunkIndex (b : ℝ) (k m : ℕ) (p : Vertex) : ℤ×ℤ :=
  (p.1/(2 : ℤ)^m,⌊transverse b p/(2 : ℝ)^k⌋)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SpatialFirstExit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

noncomputable def chunkInterior (b : ℝ) (k m : ℕ) (v : Vertex) : Prop :=
  |v.1| < 2*(2 : ℤ)^m ∧ |transverse b v| < (2 : ℝ)^k

noncomputable def FullSpatialChunk (b : ℝ) (k m : ℕ) (ds : List Step) : Prop :=
  (∀ i < ds.length, chunkInterior b k m (displacement (ds.take i))) ∧
    ¬chunkInterior b k m (displacement ds)

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SpatialChunks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

noncomputable def chunkIndexTail (b : ℝ) (k m : ℕ) : Vertex → List (List Step) → List (ℤ×ℤ)
  | _,[] => []
  | p,q::qs => spatialChunkIndex b k m (p+displacement q)::chunkIndexTail b k m (p+displacement q) qs

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SpatialBadPathCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset

def SpatialBadPath (w : Edge → ℝ) (b m₀ a η : ℝ) (k m N : ℕ) : Prop :=
  ∃ blocks : List (List Step), ∃ rest : List Step,
    blocks.length=N ∧ (∀ q ∈ blocks, FullSpatialChunk b k m q) ∧
    (∀ i ≤ rest.length, chunkInterior b k m (displacement (rest.take i))) ∧
    ((trace 0 (blocks.flatten++rest)).map traversalEdge).Nodup ∧
    defect w b m₀ a 0 (blocks.flatten++rest) < N*η*(2 : ℝ)^k/2

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_LatticeSwap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

def swapStep : Step → Step
  | .east => .north
  | .west => .south
  | .north => .east
  | .south => .west

@[simp] lemma swapStep_swap (d : Step) : swapStep (swapStep d)=d := by cases d <;> rfl
@[simp] lemma swapStep_delta (d : Step) : (swapStep d).delta=d.delta.swap := by cases d <;> rfl

def swapEdge (e : Edge) : Edge := (e.1.swap,!e.2)
@[simp] lemma swapEdge_swap (e : Edge) : swapEdge (swapEdge e)=e := by rcases e with ⟨p,b⟩; cases b <;> rfl

noncomputable def swapPlane : Plane ≃ₗᵢ[ℝ] Plane :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 1)

@[simp] lemma swapPlane_zero (v : Plane) : swapPlane v 0=v 1 := by
  simp [swapPlane,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']
@[simp] lemma swapPlane_one (v : Plane) : swapPlane v 1=v 0 := by
  simp [swapPlane,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']
@[simp] lemma swapPlane_swap (v : Plane) : swapPlane (swapPlane v)=v := by
  ext i; fin_cases i <;> simp

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SphereCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology

noncomputable def sphereChart (μ : Plane → ℝ) (c t : ℝ) : Plane :=
  (c/μ (direction t)) • direction t
noncomputable def directionRatio (v : Plane) : ℝ := v 1/v 0

end PlanarFPP

end OAI
end


