-- Prove2me | Definitions.Def_OAISPf000
-- name    : OAISPf000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T10:37:57.060932+00:00
-- url     : https://prove2.me/theorems/623fdda6-e9fe-4e53-848f-8a64bae2d8c4
-- title:
--   Definitions bundle OAISPf000 of the split of OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PlanarFPP.manuscriptMain`, carved from OpenAI's openai/math development (OpenAI, *Strict convexity and differentiability of the planar exponential first-passage limit shape*, OpenAI Math Release, September 24, 2026, result family 212, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 289 declarations of OpenAI's Lean: 78 definitions, 2 inductive types or structures, 5 instances and 204 theorems. The definitions and types are `OAI.CompanionFPP.CalibrationL2`, `OAI.CompanionFPP.DirectionalCalibration`, `OAI.CompanionFPP.DirectionalCalibration.meanHom`, `OAI.CompanionFPP.DirectionalCalibration.meanLinear`, `OAI.CompanionFPP.Edge`, `OAI.CompanionFPP.Environment`, `OAI.CompanionFPP.HasTimeConstant`, `OAI.CompanionFPP.LocalCoordinates`, `OAI.CompanionFPP.Plane`, `OAI.CompanionFPP.TimeNorm`, `OAI.CompanionFPP.Vertex`, `OAI.CompanionFPP.Weights`, `OAI.CompanionFPP.actualTimeNorm`, `OAI.CompanionFPP.approxL2`, `OAI.CompanionFPP.avoidingWalks`, `OAI.CompanionFPP.calibrationApprox`, `OAI.CompanionFPP.calibrationCovarianceSubgroup`, `OAI.CompanionFPP.candidateTrails`, `OAI.CompanionFPP.chosenCalibration`, `OAI.CompanionFPP.clipReal`, `OAI.CompanionFPP.coordinateVariance`, `OAI.CompanionFPP.directionalMeanConstant`, `OAI.CompanionFPP.edgeCost`, `OAI.CompanionFPP.embed`, `OAI.CompanionFPP.environmentLaw`, `OAI.CompanionFPP.environmentTranslation`, `OAI.CompanionFPP.exchangeCoordinate`, `OAI.CompanionFPP.extendLocalCoordinates`, `OAI.CompanionFPP.finitePassageTime`, `OAI.CompanionFPP.floorVertex`, `OAI.CompanionFPP.lattice`, `OAI.CompanionFPP.latticeDistance`, `OAI.CompanionFPP.latticeTranslation`, `OAI.CompanionFPP.localCandidates`, `OAI.CompanionFPP.localEdges`, `OAI.CompanionFPP.localPassageTime`, `OAI.CompanionFPP.meanL2`, `OAI.CompanionFPP.meanPassageSequence`, `OAI.CompanionFPP.neighbors`, `OAI.CompanionFPP.offsetTargetCocycle` and 40 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `FirstPassage_AttachmentGeometry`, `FirstPassage_BallTravel`, `FirstPassage_BoundaryGeometry`, `FirstPassage_GridMeshes`, `FirstPassage_LatticeGeometry`, `FirstPassage_LocalTravel`, `FirstPassage_Localization`, `FirstPassage_PathWitnesses`, `FirstPassage_Paths`, `FirstPassage_RareFastGeometry`, `FirstPassage_Reversal`, `FirstPassage_SpatialChunks`, `FirstPassage_SpatialModulus`, `FirstPassage_TiltedRegions`, `FirstPassage_Waypoints`, `LatticePassage_BoundedCost`, `LatticePassage_CalibrationL2`, `LatticePassage_CalibrationMean`, `LatticePassage_CalibrationShift`, `LatticePassage_CenteredLocalization`, `LatticePassage_CheapPath`, `LatticePassage_CoordinatePath`, `LatticePassage_EfronStein`, `LatticePassage_Environment`, `LatticePassage_ExponentialMoment`, `LatticePassage_FiniteProduct`, `LatticePassage_FiniteVariance`, `LatticePassage_Geodesic`, `LatticePassage_HilbertWeakCompactness`, `LatticePassage_Lattice`, `LatticePassage_LatticeMetric`, `LatticePassage_LocalCovariance`, `LatticePassage_LocalPassage`, `LatticePassage_LocalSelection`, `LatticePassage_MeanPositivity`, `LatticePassage_MeanTimeConstant`, `LatticePassage_MetricCalibration`, `LatticePassage_Model`, `LatticePassage_NaturalMoment`, `LatticePassage_OffsetCalibration`, `LatticePassage_PassageRegularity`, `LatticePassage_PathCounting`, `LatticePassage_Paths`, `LatticePassage_PlanarCalibration`, `LatticePassage_PositiveMoment`, `LatticePassage_RectangleCalibration`, `LatticePassage_ResamplingMoment`, `LatticePassage_ResamplingSymmetry`, `LatticePassage_SecondMoment`, `LatticePassage_Stationarity`, `LatticePassage_StationaryCalibration`, `LatticePassage_TimeConstantNorm`, `LatticePassage_UniformCheapPaths`, `LatticePassage_WeakCalibration`.
--
--   **Imports.** It imports the published bundle `Def_PlanarFirstPassage`.
--
--   **Imported by** (directly, in this split): the bundle `OAISPf002`.
-- source:
--   OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 212; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFirstPassage

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_Paths
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

noncomputable def transverse (b : ℝ) (z : Vertex) : ℝ := z.2 - b * z.1
noncomputable def support (b m a : ℝ) (z : Vertex) : ℝ := m * z.1 + a * transverse b z

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
-- module Solutions.OAIS_PlanarFPP.FirstPassage_Reversal
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

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_SpatialModulus
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
-- module Solutions.OAIS_PlanarFPP.FirstPassage_LatticeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory Filter Set
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

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_Localization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory Filter Set
open scoped Topology

def PathIn (p : Vertex) (ds : List Step) (S : Set Vertex) : Prop :=
  ∀ i ≤ ds.length, p+displacement (ds.take i) ∈ S

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_Waypoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

noncomputable def segmentPoint (p q : Vertex) (t : ℝ) : Plane :=
  latticeEmbed p+t • (latticeEmbed q-latticeEmbed p)

noncomputable def waypoint (p q : Vertex) (B j : ℕ) : Vertex :=
  latticeFloor (segmentPoint p q ((j : ℝ)/B))

def SegmentTube (p q : Vertex) (R : ℝ) : Set Vertex :=
  {z | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ‖latticeEmbed z-segmentPoint p q t‖ ≤ R}

@[simp] theorem waypoint_zero (p q : Vertex) (B : ℕ) : waypoint p q B 0=p := by
  simp [waypoint,segmentPoint]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_LocalTravel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped Topology

def LocalTravel (μ : Plane → ℝ) (η δ s : ℝ) (p q : Vertex) (w : Edge → ℝ) : Prop :=
  ∃ ds, p+displacement ds=q ∧ pathCost w p ds ≤ μ (latticeEmbed (q-p))+η*s ∧
    PathIn p ds (SegmentTube p q (δ*s))

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_AttachmentGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set

@[simp] theorem latticeEmbed_add (p q : Vertex) :
    latticeEmbed (p+q) = latticeEmbed p+latticeEmbed q := by
  ext i
  fin_cases i <;> simp [latticeEmbed]

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BallTravel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter Finset MeasureTheory ProbabilityTheory
open scoped Topology

def BallTravel (μ : Plane → ℝ) (D η δ s : ℝ) (w : Edge → ℝ) : Prop :=
  ∀ p q : Vertex, ‖latticeEmbed p‖ ≤ D*s → ‖latticeEmbed q‖ ≤ D*s →
    LocalTravel μ η δ s p q w

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_BoundaryGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Finset

instance instFintypeStep : Fintype Step where
  elems := {Step.east, Step.west, Step.north, Step.south}
  complete d := by cases d <;> simp

def Step.right : Step → Step
  | .east => .south | .south => .west | .west => .north | .north => .east

def Step.outward (d : Step) : Vertex := d.right.delta

abbrev SquareSide := Vertex × Step

def IsBoundarySide (S : Finset Vertex) (e : SquareSide) : Prop :=
  e.1 ∈ S ∧ e.1 + e.2.outward ∉ S

def boundarySides (S : Finset Vertex) : Finset SquareSide :=
  (S ×ˢ univ).filter (fun e => e.1 + e.2.outward ∉ S)

@[simp] theorem mem_boundarySides (S : Finset Vertex) (e : SquareSide) :
    e ∈ boundarySides S ↔ IsBoundarySide S e := by
  simp [boundarySides, IsBoundarySide]

abbrev BoundarySide (S : Finset Vertex) := {e // e ∈ boundarySides S}

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_RareFastGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset

def blockLayer (v : Vertex) : ℤ := v.1+v.2

def blockLevel (v : Vertex) : ℤ := v.1+2*v.2

def blockX (n d : ℤ) (v : Vertex) : ℤ := blockLayer v*(n+d)

noncomputable def blockY (σ S : ℝ) (v : Vertex) : ℝ := σ*(blockLevel v : ℝ)*S

noncomputable def blockRegion (b A : ℝ) (n d : ℤ) (σ S : ℝ) (v : Vertex) : Set Vertex :=
  {p | |(p.1 : ℝ)-(blockX n d v : ℝ)| ≤ (A+3)*n ∧
    |transverse b p-blockY σ S v| ≤ 4*S}

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_TiltedRegions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

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

theorem blockRegion_finite (b A : ℝ) (n d : ℤ) (σ S : ℝ) (v : Vertex) :
    (blockRegion b A n d σ S v).Finite :=
  finite_tilted_rectangle b (blockX n d v) (blockY σ S v) ((A+3)*n) (4*S)

noncomputable def blockVertices (b A : ℝ) (n d : ℤ) (σ S : ℝ) (v : Vertex) : Finset Vertex :=
  (blockRegion_finite b A n d σ S v).toFinset

@[simp] theorem mem_blockVertices (b A : ℝ) (n d : ℤ) (σ S : ℝ) (v p : Vertex) :
    p ∈ blockVertices b A n d σ S v ↔ p ∈ blockRegion b A n d σ S v :=
  (blockRegion_finite b A n d σ S v).mem_toFinset

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_GridMeshes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Filter Set MeasureTheory
open scoped Topology

def gridLastLevel (m : ℕ) : ℕ := (m+2)/4

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.FirstPassage_PathWitnesses
attribute [-instance] _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP

abbrev Traversal := Vertex × Step

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_Paths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP

variable {V : Type*} {G : SimpleGraph V}

abbrev Weights (G : SimpleGraph V) := G.edgeSet → ℝ

def edgeCost (w : Weights G) {x y : V} (h : G.Adj x y) : ℝ :=
  w ⟨s(x, y), h⟩

@[simp] theorem edgeCost_symm (w : Weights G) {x y : V} (h : G.Adj x y) :
    edgeCost w h.symm = edgeCost w h := by
  simp only [edgeCost, Sym2.eq_swap]

def pathCost (w : Weights G) {x y : V} : G.Walk x y → ℝ
  | .nil => 0
  | .cons h p => edgeCost w h + pathCost w p

@[simp] theorem pathCost_nil (w : Weights G) (x : V) :
    pathCost w (SimpleGraph.Walk.nil : G.Walk x x) = 0 := rfl

@[simp] theorem pathCost_cons (w : Weights G) {x y z : V}
    (h : G.Adj x y) (p : G.Walk y z) :
    pathCost w (.cons h p) = edgeCost w h + pathCost w p := rfl

@[simp] theorem pathCost_append (w : Weights G) {x y z : V}
    (p : G.Walk x y) (q : G.Walk y z) :
    pathCost w (p.append q) = pathCost w p + pathCost w q := by
  induction p with
  | nil => simp
  | cons h p ih => simp [ih, add_assoc]

theorem pathCost_nonneg (w : Weights G) (hw : ∀ e, 0 ≤ w e)
    {x y : V} (p : G.Walk x y) : 0 ≤ pathCost w p := by
  induction p with
  | nil => exact le_refl 0
  | cons h p ih => exact add_nonneg (hw _) ih

noncomputable def passageTime (w : Weights G) (x y : V) : ℝ :=
  sInf (Set.range (fun p : G.Walk x y => pathCost w p))

theorem passageTime_le_pathCost (w : Weights G) (hw : ∀ e, 0 ≤ w e)
    {x y : V} (p : G.Walk x y) : passageTime w x y ≤ pathCost w p := by
  apply csInf_le
  · exact ⟨0, by rintro _ ⟨q, rfl⟩; exact pathCost_nonneg w hw q⟩
  · exact ⟨p, rfl⟩

@[simp] theorem pathCost_reverse (w : Weights G) {x y : V} (p : G.Walk x y) :
    pathCost w p.reverse = pathCost w p := by
  induction p with
  | nil => simp
  | cons h p ih =>
    simp [SimpleGraph.Walk.reverse_cons, ih, edgeCost, Sym2.eq_swap, add_comm]

theorem passageTime_nonneg (w : Weights G) (hw : ∀ e, 0 ≤ w e)
    {x y : V} (hp : Nonempty (G.Walk x y)) : 0 ≤ passageTime w x y := by
  obtain ⟨p⟩ := hp
  apply le_csInf (s := Set.range (fun p : G.Walk x y => pathCost w p)) ⟨_, ⟨p, rfl⟩⟩
  rintro _ ⟨q, rfl⟩
  exact pathCost_nonneg w hw q

@[simp] theorem passageTime_self (w : Weights G) (hw : ∀ e, 0 ≤ w e) (x : V) :
    passageTime w x x = 0 := by
  apply le_antisymm
  · simpa using passageTime_le_pathCost w hw (SimpleGraph.Walk.nil : G.Walk x x)
  · exact passageTime_nonneg w hw ⟨.nil⟩

theorem passageTime_symm (w : Weights G) (x y : V) :
    passageTime w x y = passageTime w y x := by
  unfold passageTime
  congr 1
  ext t
  constructor <;> rintro ⟨p, rfl⟩ <;> exact ⟨p.reverse, pathCost_reverse w p⟩

theorem passageTime_triangle (w : Weights G) (hw : ∀ e, 0 ≤ w e)
    {x y z : V} (hxy : Nonempty (G.Walk x y)) (hyz : Nonempty (G.Walk y z)) :
    passageTime w x z ≤ passageTime w x y + passageTime w y z := by
  obtain ⟨p₀⟩ := hxy
  obtain ⟨q₀⟩ := hyz
  suffices h : passageTime w x z - passageTime w x y ≤ passageTime w y z by linarith
  apply le_csInf (s := Set.range (fun q : G.Walk y z => pathCost w q)) ⟨_, ⟨q₀, rfl⟩⟩
  rintro _ ⟨q, rfl⟩
  suffices h : passageTime w x z - pathCost w q ≤ passageTime w x y by linarith
  apply le_csInf (s := Set.range (fun p : G.Walk x y => pathCost w p)) ⟨_, ⟨p₀, rfl⟩⟩
  rintro _ ⟨p, rfl⟩
  have h := passageTime_le_pathCost w hw (p.append q)
  rw [pathCost_append] at h
  linarith

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Filter Topology

abbrev Vertex := ℤ × ℤ
abbrev Plane := ℝ × ℝ

def lattice : SimpleGraph Vertex where
  Adj x y := |x.1 - y.1| + |x.2 - y.2| = 1
  symm := ⟨by intros x y h; simpa only [abs_sub_comm] using h⟩
  loopless := ⟨by intro x; simp⟩

abbrev Edge := lattice.edgeSet
abbrev Environment := Weights lattice

noncomputable instance expOneProbability : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

noncomputable def environmentLaw : Measure Environment :=
  Measure.infinitePi (fun _ : Edge => expMeasure 1)

def embed (x : Vertex) : Plane := ((x.1 : ℝ), (x.2 : ℝ))

def scaleVertex (n : ℕ) (x : Vertex) : Vertex := ((n : ℤ) * x.1, (n : ℤ) * x.2)

structure TimeNorm where
  seminorm : Seminorm ℝ Plane
  definite : ∀ x, seminorm x = 0 → x = 0

def HasTimeConstant (μ : TimeNorm) : Prop :=
  ∀ᵐ ω ∂environmentLaw, ∀ x : Vertex,
    Tendsto (fun n : ℕ => passageTime ω (0, 0) (scaleVertex n x) / (n : ℝ))
      atTop (𝓝 (μ.seminorm (embed x)))

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_Environment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Set

noncomputable instance environmentProbability : IsProbabilityMeasure environmentLaw :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi (fun _ : Edge => expMeasure 1)))

theorem edge_marginal (e : Edge) :
    Measure.map (fun ω : Environment => ω e) environmentLaw = expMeasure 1 :=
  Measure.infinitePi_map_eval _ e

theorem exponential_positive : ∀ᵐ x ∂expMeasure 1, 0 < x := by
  have hc : (expMeasure 1 (Iic 0)).toReal = 0 := by
    rw [← measureReal_def, ← cdf_eq_real]
    simp [cdf_expMeasure_eq (r := 1) (by norm_num)]
  have hz : expMeasure 1 (Iic 0) = 0 :=
    (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.zero_ne_top).mp
      (by simpa using hc)
  simpa only [ae_iff, not_lt, Iic] using hz

theorem all_edge_weights_positive : ∀ᵐ ω ∂environmentLaw, ∀ e, 0 < ω e := by
  rw [ae_all_iff]
  intro e
  exact (measurePreserving_eval_infinitePi (fun _ : Edge => expMeasure 1) e).quasiMeasurePreserving.ae exponential_positive

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_ExponentialMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

lemma weighted_exponential_density (x : ℝ) :
    exponentialPDF 1 x * ENNReal.ofReal (exp (-5 * x)) =
      ENNReal.ofReal (1 / 6 : ℝ) * exponentialPDF 6 x := by
  by_cases hx : 0 ≤ x
  · rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hx]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    simp only [one_mul]
    calc
      exp (-x) * exp (-5 * x) = exp (-(6 * x)) := by
        rw [← exp_add]
        congr 1
        ring
      _ = (1 / 6 : ℝ) * (6 * exp (-(6 * x))) := by ring
  · rw [exponentialPDF_of_neg (lt_of_not_ge hx),
      exponentialPDF_of_neg (lt_of_not_ge hx)]
    simp

theorem exponential_laplace_five :
    (∫⁻ x, ENNReal.ofReal (exp (-5 * x)) ∂expMeasure 1) = ENNReal.ofReal (1 / 6 : ℝ) := by
  change (∫⁻ x, ENNReal.ofReal (exp (-5 * x)) ∂volume.withDensity (exponentialPDF 1)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume (by
    unfold exponentialPDF; fun_prop) (by fun_prop)]
  simp only [Pi.mul_apply, weighted_exponential_density]
  rw [lintegral_const_mul _ (by unfold exponentialPDF; fun_prop),
    lintegral_exponentialPDF_eq_one (by norm_num : (0 : ℝ) < 6), mul_one]

theorem edge_set_laplace (s : Finset Edge) :
    (∫⁻ ω : Environment, ∏ e ∈ s, ENNReal.ofReal (exp (-5 * ω e)) ∂environmentLaw) =
      ENNReal.ofReal (1 / 6 : ℝ) ^ s.card := by
  have hind : iIndepFun (fun e (ω : Environment) => ENNReal.ofReal (exp (-5 * ω e)))
      environmentLaw := iIndepFun_infinitePi (X := fun _ (x : ℝ) =>
        ENNReal.ofReal (exp (-5 * x))) (by intro i; fun_prop)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun s _ hind (by intro i; fun_prop)]
  have he : ∀ e : Edge, (∫⁻ ω : Environment, ENNReal.ofReal (exp (-5 * ω e))
      ∂environmentLaw) = ENNReal.ofReal (1 / 6 : ℝ) := by
    intro e
    rw [← lintegral_map (by fun_prop : Measurable (fun x : ℝ =>
      ENNReal.ofReal (exp (-5 * x)))) (measurable_pi_apply e), edge_marginal]
    exact exponential_laplace_five
  simp only [he, prod_const]

lemma edge_set_exp_sum (s : Finset Edge) (ω : Environment) :
    ENNReal.ofReal (exp (-5 * ∑ e ∈ s, ω e)) =
      ∏ e ∈ s, ENNReal.ofReal (exp (-5 * ω e)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s he ih =>
    rw [sum_insert he, prod_insert he, mul_add, exp_add,
      ENNReal.ofReal_mul (exp_pos _).le, ih]

theorem edge_set_sum_laplace (s : Finset Edge) :
    (∫⁻ ω : Environment, ENNReal.ofReal (exp (-5 * ∑ e ∈ s, ω e)) ∂environmentLaw) =
      ENNReal.ofReal (1 / 6 : ℝ) ^ s.card := by
  simp_rw [edge_set_exp_sum]
  exact edge_set_laplace s

theorem cheap_edge_set_probability (s : Finset Edge) (t : ℝ) :
    environmentLaw {ω : Environment | (∑ e ∈ s, ω e) ≤ t} ≤
      ENNReal.ofReal (1 / 6 : ℝ) ^ s.card / ENNReal.ofReal (exp (-5 * t)) := by
  have hm := meas_ge_le_lintegral_div (μ := environmentLaw)
    (f := fun ω : Environment => ENNReal.ofReal (exp (-5 * ∑ e ∈ s, ω e)))
    (by fun_prop) (ε := ENNReal.ofReal (exp (-5 * t)))
    (by positivity) ENNReal.ofReal_ne_top
  have hs : {ω : Environment | ENNReal.ofReal (exp (-5 * t)) ≤
      ENNReal.ofReal (exp (-5 * ∑ e ∈ s, ω e))} =
      {ω : Environment | (∑ e ∈ s, ω e) ≤ t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, ENNReal.ofReal_le_ofReal_iff (exp_pos _).le,
      exp_le_exp]
    constructor <;> intro h <;> linarith
  rw [hs, edge_set_sum_laplace] at hm
  exact hm

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_CheapPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V}

def pathEdges {x y : V} : G.Walk x y → List G.edgeSet
  | .nil => []
  | .cons h p => ⟨s(_, _), h⟩ :: pathEdges p

lemma pathEdges_val {x y : V} (p : G.Walk x y) :
    (pathEdges p).map Subtype.val = p.edges := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [pathEdges, ih]

lemma pathEdges_length {x y : V} (p : G.Walk x y) :
    (pathEdges p).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [pathEdges, ih]

lemma pathEdges_nodup {x y : V} {p : G.Walk x y} (hp : p.IsTrail) :
    (pathEdges p).Nodup := by
  apply List.Nodup.of_map (f := Subtype.val)
  rw [pathEdges_val]
  exact hp.edges_nodup

lemma pathCost_eq_edgeList_sum (ω : Weights G) {x y : V} (p : G.Walk x y) :
    pathCost ω p = ((pathEdges p).map ω).sum := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [pathEdges, pathCost, edgeCost, ih]

theorem cheap_trail_probability {x y : Vertex} (p : lattice.Walk x y) (hp : p.IsTrail)
    (t : ℝ) : environmentLaw {ω : Environment | pathCost ω p ≤ t} ≤
      ENNReal.ofReal (1 / 6 : ℝ) ^ p.length / ENNReal.ofReal (exp (-5 * t)) := by
  classical
  have hn := pathEdges_nodup hp
  have hc : (pathEdges p).toFinset.card = p.length := by
    rw [List.toFinset_card_of_nodup hn, pathEdges_length]
  have he : ∀ ω : Environment, (∑ e ∈ (pathEdges p).toFinset, ω e) = pathCost ω p := by
    intro ω
    rw [pathCost_eq_edgeList_sum]
    exact List.sum_toFinset _ hn
  have h := cheap_edge_set_probability (pathEdges p).toFinset t
  simpa only [he, hc] using h

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_Lattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP

theorem horizontal_nat (a b : ℤ) (n : ℕ) :
    Nonempty (lattice.Walk (a, b) (a + (n : ℤ), b)) := by
  induction n with
  | zero => simpa using (show Nonempty (lattice.Walk (a,b) (a,b)) from ⟨.nil⟩)
  | succ n ih =>
    obtain ⟨p⟩ := ih
    have h : lattice.Adj (a + (n : ℤ), b) (a + ((n+1 : ℕ) : ℤ), b) := by
      change |a + (n : ℤ) - (a + ((n+1 : ℕ) : ℤ))| + |b - b| = 1
      simp
    exact ⟨p.concat h⟩

theorem vertical_nat (a b : ℤ) (n : ℕ) :
    Nonempty (lattice.Walk (a, b) (a, b + (n : ℤ))) := by
  induction n with
  | zero => simpa using (show Nonempty (lattice.Walk (a,b) (a,b)) from ⟨.nil⟩)
  | succ n ih =>
    obtain ⟨p⟩ := ih
    have h : lattice.Adj (a, b + (n : ℤ)) (a, b + ((n+1 : ℕ) : ℤ)) := by
      change |a - a| + |b + (n : ℤ) - (b + ((n+1 : ℕ) : ℤ))| = 1
      simp
    exact ⟨p.concat h⟩

theorem horizontal_walk (a c b : ℤ) : Nonempty (lattice.Walk (a,b) (c,b)) := by
  by_cases h : a ≤ c
  · have he : a + ((c-a).toNat : ℤ) = c := by omega
    simpa only [he] using horizontal_nat a b (c-a).toNat
  · have he : c + ((a-c).toNat : ℤ) = a := by omega
    have hp : Nonempty (lattice.Walk (c,b) (a,b)) := by
      simpa only [he] using horizontal_nat c b (a-c).toNat
    obtain ⟨p⟩ := hp
    exact ⟨p.reverse⟩

theorem vertical_walk (a b c : ℤ) : Nonempty (lattice.Walk (a,b) (a,c)) := by
  by_cases h : b ≤ c
  · have he : b + ((c-b).toNat : ℤ) = c := by omega
    simpa only [he] using vertical_nat a b (c-b).toNat
  · have he : c + ((b-c).toNat : ℤ) = b := by omega
    have hp : Nonempty (lattice.Walk (a,c) (a,b)) := by
      simpa only [he] using vertical_nat a c (b-c).toNat
    obtain ⟨p⟩ := hp
    exact ⟨p.reverse⟩

theorem lattice_walk (x y : Vertex) : Nonempty (lattice.Walk x y) := by
  obtain ⟨p⟩ := horizontal_walk x.1 y.1 x.2
  obtain ⟨q⟩ := vertical_walk y.1 x.2 y.2
  exact ⟨p.append q⟩

theorem passageTime_properties : ∀ᵐ ω ∂environmentLaw,
    (∀ x y, 0 ≤ passageTime ω x y) ∧
    (∀ x, passageTime ω x x = 0) ∧
    (∀ x y, passageTime ω x y = passageTime ω y x) ∧
    (∀ x y z, passageTime ω x z ≤ passageTime ω x y + passageTime ω y z) := by
  filter_upwards [all_edge_weights_positive] with ω hω
  have hn : ∀ e, 0 ≤ ω e := fun e => (hω e).le
  exact ⟨fun x y => passageTime_nonneg ω hn (lattice_walk x y),
    passageTime_self ω hn, passageTime_symm ω,
    fun x y z => passageTime_triangle ω hn (lattice_walk x y) (lattice_walk y z)⟩

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_PathCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open Finset

def neighbors (x : Vertex) : Finset Vertex :=
  {(x.1 + 1, x.2), (x.1 - 1, x.2), (x.1, x.2 + 1), (x.1, x.2 - 1)}

theorem mem_neighbors {x y : Vertex} : y ∈ neighbors x ↔ lattice.Adj x y := by
  rcases x with ⟨a,b⟩
  rcases y with ⟨c,d⟩
  change (c,d) ∈ neighbors (a,b) ↔ |a-c| + |b-d| = 1
  simp only [neighbors, mem_insert, mem_singleton, Prod.mk.injEq]
  rcases le_total 0 (a-c) with ha | ha <;>
    rcases le_total 0 (b-d) with hb | hb
  all_goals simp only [abs_of_nonneg, abs_of_nonpos, ha, hb]
  all_goals omega

theorem card_neighbors (x : Vertex) : (neighbors x).card = 4 := by
  have h₁ : (x.1 + 1, x.2) ≠ (x.1 - 1, x.2) := by intro h; have := congrArg Prod.fst h; omega
  have h₂ : (x.1 + 1, x.2) ≠ (x.1, x.2 + 1) := by intro h; have := congrArg Prod.fst h; omega
  have h₃ : (x.1 + 1, x.2) ≠ (x.1, x.2 - 1) := by intro h; have := congrArg Prod.fst h; omega
  have h₄ : (x.1 - 1, x.2) ≠ (x.1, x.2 + 1) := by intro h; have := congrArg Prod.fst h; omega
  have h₅ : (x.1 - 1, x.2) ≠ (x.1, x.2 - 1) := by intro h; have := congrArg Prod.fst h; omega
  have h₆ : (x.1, x.2 + 1) ≠ (x.1, x.2 - 1) := by intro h; have := congrArg Prod.snd h; omega
  simp [neighbors, h₁,h₂,h₃,h₄,h₅,h₆]

theorem card_neighbors_erase {prev x : Vertex} (h : lattice.Adj x prev) :
    ((neighbors x).erase prev).card = 3 := by
  rw [card_erase_of_mem (mem_neighbors.mpr h), card_neighbors]

noncomputable def avoidingWalks (n : ℕ) (prev x : Vertex) :
    Finset (Σ y : Vertex, lattice.Walk x y) := by
  classical
  exact match n with
  | 0 => {⟨x, .nil⟩}
  | n+1 => ((neighbors x).erase prev).attach.biUnion fun v =>
      (avoidingWalks n x v).image fun q =>
        ⟨q.1, .cons (mem_neighbors.mp (mem_of_mem_erase v.property)) q.2⟩

theorem card_avoidingWalks (n : ℕ) {prev x : Vertex} (h : lattice.Adj x prev) :
    (avoidingWalks n prev x).card ≤ 3^n := by
  classical
  induction n generalizing prev x with
  | zero => simp [avoidingWalks]
  | succ n ih =>
    calc
      _ ≤ ∑ v ∈ ((neighbors x).erase prev).attach,
          ((avoidingWalks n x v).image (fun q =>
            (⟨q.1, .cons (mem_neighbors.mp (mem_of_mem_erase v.property)) q.2⟩ :
              Σ y : Vertex, lattice.Walk x y))).card := card_biUnion_le
      _ ≤ ∑ _v ∈ ((neighbors x).erase prev).attach, 3^n := by
        apply sum_le_sum
        intro v hv
        exact card_image_le.trans (ih (mem_neighbors.mp (mem_of_mem_erase v.property)).symm)
      _ = 3^(n+1) := by
        simp [card_neighbors_erase h, pow_succ, Nat.mul_comm]

theorem trail_mem_avoiding {prev x y : Vertex} (p : lattice.Walk x y)
    (hp : p.IsTrail) (hne : s(prev,x) ∉ p.edges) :
    (⟨y,p⟩ : Σ y : Vertex, lattice.Walk x y) ∈ avoidingWalks p.length prev x := by
  classical
  induction p generalizing prev with
  | nil => simp [avoidingWalks]
  | @cons x v y h p ih =>
    have ht : p.IsTrail := hp.of_cons
    have hnot : s(x,v) ∉ p.edges := (List.nodup_cons.mp hp.edges_nodup).1
    have hvne : v ≠ prev := by
      intro heq
      subst v
      apply hne
      simp [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
    have hv : v ∈ (neighbors x).erase prev := mem_erase.mpr ⟨hvne, mem_neighbors.mpr h⟩
    simp only [SimpleGraph.Walk.length_cons, avoidingWalks, mem_biUnion]
    refine ⟨⟨v,hv⟩, mem_attach _ _, ?_⟩
    exact mem_image.mpr ⟨⟨y,p⟩, ih ht hnot, rfl⟩

noncomputable def startingWalks (n : ℕ) (x : Vertex) :
    Finset (Σ y : Vertex, lattice.Walk x y) := by
  classical
  exact match n with
  | 0 => {⟨x, .nil⟩}
  | n+1 => (neighbors x).attach.biUnion fun v =>
      (avoidingWalks n x v).image fun q =>
        ⟨q.1, .cons (mem_neighbors.mp v.property) q.2⟩

theorem card_startingWalks (n : ℕ) (x : Vertex) :
    (startingWalks (n+1) x).card ≤ 4 * 3^n := by
  classical
  calc
    _ ≤ ∑ v ∈ (neighbors x).attach,
        ((avoidingWalks n x v).image (fun q =>
          (⟨q.1, .cons (mem_neighbors.mp v.property) q.2⟩ :
            Σ y : Vertex, lattice.Walk x y))).card := card_biUnion_le
    _ ≤ ∑ _v ∈ (neighbors x).attach, 3^n := by
      apply sum_le_sum
      intro v hv
      exact card_image_le.trans (card_avoidingWalks n (mem_neighbors.mp v.property).symm)
    _ = 4 * 3^n := by simp [card_neighbors]

theorem trail_mem_starting {x y : Vertex} (p : lattice.Walk x y) (hp : p.IsTrail) :
    (⟨y,p⟩ : Σ y : Vertex, lattice.Walk x y) ∈ startingWalks p.length x := by
  classical
  cases p with
  | nil => simp [startingWalks]
  | @cons x v y h p =>
    have hnot : s(x,v) ∉ p.edges := (List.nodup_cons.mp hp.edges_nodup).1
    simp only [SimpleGraph.Walk.length_cons, startingWalks, mem_biUnion]
    refine ⟨⟨v,mem_neighbors.mpr h⟩, mem_attach _ _, ?_⟩
    exact mem_image.mpr ⟨⟨y,p⟩, trail_mem_avoiding p hp.of_cons hnot, rfl⟩

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_UniformCheapPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

noncomputable def candidateTrails (n : ℕ) (x : Vertex) :
    Finset (Σ y : Vertex, lattice.Walk x y) := by
  classical
  exact (startingWalks n x).filter fun q => q.2.IsTrail ∧ q.2.length = n

theorem cheap_fixed_length (n : ℕ) (x : Vertex) (t : ℝ) :
    environmentLaw {ω : Environment | ∃ y, ∃ (p : lattice.Walk x y),
      p.IsTrail ∧ p.length = n+1 ∧ pathCost ω p ≤ t} ≤
    ((4 * 3^n : ℕ) : ℝ≥0∞) *
      (ENNReal.ofReal (1 / 6 : ℝ) ^ (n+1) / ENNReal.ofReal (exp (-5 * t))) := by
  classical
  let S := candidateTrails (n+1) x
  have hs (q : Σ y : Vertex, lattice.Walk x y) (hq : q ∈ S) :
      q.2.IsTrail ∧ q.2.length = n+1 := (mem_filter.mp hq).2
  have hcard : S.card ≤ 4 * 3^n := (card_filter_le _ _).trans (card_startingWalks n x)
  calc
    _ ≤ environmentLaw (⋃ q ∈ S, {ω : Environment | pathCost ω q.2 ≤ t}) := by
      apply measure_mono
      rintro ω ⟨y,p,hp,hl,hcost⟩
      have hmem : (⟨y,p⟩ : Σ y : Vertex, lattice.Walk x y) ∈ S := by
        apply mem_filter.mpr
        exact ⟨hl ▸ trail_mem_starting p hp, hp, hl⟩
      exact Set.mem_iUnion.mpr ⟨⟨y,p⟩, Set.mem_iUnion.mpr ⟨hmem,hcost⟩⟩
    _ ≤ ∑ q ∈ S, environmentLaw {ω : Environment | pathCost ω q.2 ≤ t} :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ S, (ENNReal.ofReal (1 / 6 : ℝ) ^ (n+1) /
        ENNReal.ofReal (exp (-5 * t))) := by
      apply sum_le_sum
      intro q hq
      simpa only [(hs q hq).2] using cheap_trail_probability q.2 (hs q hq).1 t
    _ = (S.card : ℝ≥0∞) * (ENNReal.ofReal (1 / 6 : ℝ) ^ (n+1) /
        ENNReal.ofReal (exp (-5 * t))) := by simp
    _ ≤ _ := by gcongr

theorem cheap_long_trail_one_start (n : ℕ) (x : Vertex) (t : ℝ) :
    environmentLaw {ω : Environment | ∃ y, ∃ (p : lattice.Walk x y),
      p.IsTrail ∧ n+1 ≤ p.length ∧ pathCost ω p ≤ t} ≤
    ((4 * 3^n : ℕ) : ℝ≥0∞) *
      (ENNReal.ofReal (1 / 6 : ℝ) ^ (n+1) / ENNReal.ofReal (exp (-5 * t))) := by
  apply le_trans _ (cheap_fixed_length n x t)
  apply measure_mono_ae
  filter_upwards [all_edge_weights_positive] with ω hω
  rintro ⟨y,p,hp,hl,hcost⟩
  have he := p.append_take_drop_eq (n+1)
  have ht : (p.take (n+1)).IsTrail :=
    SimpleGraph.Walk.IsTrail.of_append_left (q := p.drop (n+1)) (by simpa only [he] using hp)
  have hlen : (p.take (n+1)).length = n+1 := by
    rw [SimpleGraph.Walk.take_length, inf_eq_left.mpr hl]
  have hcost' : pathCost ω (p.take (n+1)) ≤ pathCost ω p := by
    have hn := pathCost_nonneg ω (fun e => (hω e).le) (p.drop (n+1))
    have hc := congrArg (pathCost ω) he
    rw [pathCost_append] at hc
    linarith
  exact ⟨_, p.take (n+1), ht, hlen, hcost'.trans hcost⟩

theorem no_long_cheap_trails (V : Finset Vertex) (n : ℕ) (t : ℝ) :
    environmentLaw {ω : Environment | ∃ x ∈ V, ∃ y, ∃ (p : lattice.Walk x y),
      p.IsTrail ∧ n+1 ≤ p.length ∧ pathCost ω p ≤ t} ≤
    (V.card : ℝ≥0∞) * (((4 * 3^n : ℕ) : ℝ≥0∞) *
      (ENNReal.ofReal (1 / 6 : ℝ) ^ (n+1) / ENNReal.ofReal (exp (-5 * t)))) := by
  calc
    _ = environmentLaw (⋃ x ∈ V, {ω : Environment | ∃ y, ∃ (p : lattice.Walk x y),
        p.IsTrail ∧ n+1 ≤ p.length ∧ pathCost ω p ≤ t}) := by
      congr 1
      ext ω
      simp
    _ ≤ ∑ x ∈ V, environmentLaw {ω : Environment | ∃ y, ∃ (p : lattice.Walk x y),
        p.IsTrail ∧ n+1 ≤ p.length ∧ pathCost ω p ≤ t} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ V, (((4 * 3^n : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal (1 / 6 : ℝ) ^ (n+1) / ENNReal.ofReal (exp (-5 * t)))) :=
      sum_le_sum (fun x _ => cheap_long_trail_one_start n x t)
    _ = _ := by simp

lemma count_laplace_identity (n : ℕ) (t : ℝ) :
    ((4 * 3^n : ℕ) : ℝ) * ((1 / 6 : ℝ)^(n+1) / exp (-5 * t)) =
      (4 / 3 : ℝ) * exp (5*t) * (1 / 2 : ℝ)^(n+1) := by
  have hpow : (3 : ℝ)^n * (1 / 6 : ℝ)^n = (1 / 2 : ℝ)^n := by
    rw [← mul_pow]
    norm_num
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [neg_mul, exp_neg, div_eq_mul_inv, inv_inv]
  rw [pow_succ, pow_succ]
  calc
    _ = (4 * (3^n * (1 / 6 : ℝ)^n) * (1 / 6)) * exp (5*t) := by ring
    _ = _ := by rw [hpow]; ring

theorem no_long_cheap_paths (V : Finset Vertex) (R : ℕ) (hR : 1 ≤ R)
    (t : ℝ) (_ht : 0 ≤ t) :
    environmentLaw.real {ω : Environment | ∃ x ∈ V, ∃ y, ∃ (p : lattice.Walk x y),
      p.IsPath ∧ R ≤ p.length ∧ pathCost ω p ≤ t} ≤
      (8 / 3 : ℝ) * V.card * exp (5*t) * (1 / 2 : ℝ)^R := by
  cases R with
  | zero => omega
  | succ n =>
    have h := (measure_mono (μ := environmentLaw) (show
        {ω : Environment | ∃ x ∈ V, ∃ y, ∃ (p : lattice.Walk x y),
          p.IsPath ∧ n+1 ≤ p.length ∧ pathCost ω p ≤ t} ⊆
        {ω : Environment | ∃ x ∈ V, ∃ y, ∃ (p : lattice.Walk x y),
          p.IsTrail ∧ n+1 ≤ p.length ∧ pathCost ω p ≤ t} from by
          rintro ω ⟨x,hx,y,p,hp,hl,hc⟩
          exact ⟨x,hx,y,p,hp.isTrail,hl,hc⟩)).trans (no_long_cheap_trails V n t)
    have hne : ENNReal.ofReal (exp (-5*t)) ≠ 0 := by positivity
    have hfin : (V.card : ℝ≥0∞) * (((4 * 3^n : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal (1 / 6 : ℝ)^(n+1) / ENNReal.ofReal (exp (-5*t)))) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.div_ne_top (by simp) hne))
    have hr := ENNReal.toReal_mono hfin h
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
      ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 6),
      ENNReal.toReal_ofReal (exp_pos _).le] at hr
    rw [count_laplace_identity] at hr
    change environmentLaw.real _ ≤ _ at hr
    apply hr.trans
    have hn : (0 : ℝ) ≤ (V.card : ℝ) * exp (5*t) * (1 / 2 : ℝ)^(n+1) := by positivity
    nlinarith

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_BoundedCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Filter Topology

theorem unbounded_cheap_paths_null (x : Vertex) (m : ℕ) :
    environmentLaw {ω : Environment | ∀ R : ℕ, ∃ y, ∃ (p : lattice.Walk x y),
      p.IsPath ∧ R ≤ p.length ∧ pathCost ω p ≤ (m : ℝ)} = 0 := by
  let E := {ω : Environment | ∀ R : ℕ, ∃ y, ∃ (p : lattice.Walk x y),
      p.IsPath ∧ R ≤ p.length ∧ pathCost ω p ≤ (m : ℝ)}
  have hb (n : ℕ) : environmentLaw.real E ≤
      (8 / 3 : ℝ) * exp (5 * (m : ℝ)) * (1 / 2 : ℝ)^(n+1) := by
    have hsub : E ⊆ {ω : Environment | ∃ z ∈ ({x} : Finset Vertex), ∃ y,
        ∃ (p : lattice.Walk z y), p.IsPath ∧ n+1 ≤ p.length ∧ pathCost ω p ≤ (m : ℝ)} := by
      intro ω hω
      obtain ⟨y,p,hp,hl,hc⟩ := hω (n+1)
      exact ⟨x, by simp, y,p,hp,hl,hc⟩
    have hle := ENNReal.toReal_mono (measure_ne_top environmentLaw _) (measure_mono (μ := environmentLaw) hsub)
    have h := no_long_cheap_paths ({x} : Finset Vertex) (n+1) (by omega) m (by positivity)
    exact hle.trans (by simpa [measureReal_def] using h)
  have ht : Tendsto (fun n : ℕ =>
      (8 / 3 : ℝ) * exp (5 * (m : ℝ)) * (1 / 2 : ℝ)^(n+1)) atTop (𝓝 0) := by
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)).mul_const (1/2 : ℝ)
    simpa only [← pow_succ, zero_mul, mul_zero] using hp.const_mul ((8/3 : ℝ) * exp (5*(m:ℝ)))
  have hz : environmentLaw.real E = 0 :=
    le_antisymm (ge_of_tendsto ht (Eventually.of_forall hb)) ENNReal.toReal_nonneg
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.zero_ne_top).mp
  simpa [measureReal_def, E] using hz

theorem bounded_cost_path_lengths : ∀ᵐ ω ∂environmentLaw, ∀ x : Vertex, ∀ m : ℕ,
    ∃ R : ℕ, ∀ y, ∀ p : lattice.Walk x y,
      p.IsPath → pathCost ω p ≤ (m : ℝ) → p.length < R := by
  rw [ae_all_iff]
  intro x
  rw [ae_all_iff]
  intro m
  have ha : ∀ᵐ ω ∂environmentLaw, ¬ (∀ R : ℕ, ∃ y, ∃ (p : lattice.Walk x y),
      p.IsPath ∧ R ≤ p.length ∧ pathCost ω p ≤ (m : ℝ)) := by
    simpa only [ae_iff, not_not] using unbounded_cheap_paths_null x m
  filter_upwards [ha] with ω hω
  obtain ⟨R,hR⟩ := not_forall.mp hω
  refine ⟨R, ?_⟩
  intro y p hp hc
  by_contra hlen
  exact hR ⟨y,p,hp, Nat.le_of_not_gt hlen,hc⟩

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_Geodesic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory Finset

variable {V : Type*} {G : SimpleGraph V}

lemma pathCost_eq_darts_sum (w : Weights G) {x y : V} (p : G.Walk x y) :
    pathCost w p = (p.darts.map (fun d => edgeCost w d.adj)).sum := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [ih, edgeCost]

theorem bypass_cost_le [DecidableEq V] (w : Weights G) (hw : ∀ e, 0 ≤ w e)
    {x y : V} (p : G.Walk x y) : pathCost w p.bypass ≤ pathCost w p := by
  rw [pathCost_eq_darts_sum, pathCost_eq_darts_sum]
  apply (p.darts_bypass_sublist_darts.map (fun d => edgeCost w d.adj)).sum_le_sum
  intro a ha
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp ha
  exact hw _

theorem exists_geodesic_of_bounded_cost (ω : Environment) (hw : ∀ e, 0 ≤ ω e)
    (x y : Vertex)
    (hbound : ∀ m : ℕ, ∃ R : ℕ, ∀ z, ∀ p : lattice.Walk x z,
      p.IsPath → pathCost ω p ≤ (m : ℝ) → p.length < R) :
    ∃ p : lattice.Walk x y, p.IsPath ∧ pathCost ω p = passageTime ω x y := by
  classical
  obtain ⟨q⟩ := lattice_walk x y
  obtain ⟨m,hm⟩ := exists_nat_gt (pathCost ω q)
  obtain ⟨R,hR⟩ := hbound m
  let S : Finset (Σ z : Vertex, lattice.Walk x z) :=
    (range R).biUnion fun n => startingWalks n x
  let C : Set ℝ := {c | ∃ p : lattice.Walk x y,
    p.IsPath ∧ pathCost ω p ≤ (m : ℝ) ∧ c = pathCost ω p}
  have hC : C.Finite := by
    apply (S.image (fun q => pathCost ω q.2)).finite_toSet.subset
    rintro c ⟨p,hp,hpm,rfl⟩
    apply mem_image.mpr
    refine ⟨⟨y,p⟩, ?_, rfl⟩
    exact mem_biUnion.mpr ⟨p.length, mem_range.mpr (hR y p hp hpm), trail_mem_starting p hp.isTrail⟩
  have hne : C.Nonempty :=
    ⟨pathCost ω q.bypass, q.bypass, q.bypass_isPath, (bypass_cost_le ω hw q).trans hm.le, rfl⟩
  obtain ⟨c,hc,hmin⟩ := Set.exists_min_image C id hC hne
  obtain ⟨p,hp,hpm,rfl⟩ := hc
  have hleast : ∀ r : lattice.Walk x y, pathCost ω p ≤ pathCost ω r := by
    intro r
    by_cases hr : pathCost ω r ≤ (m : ℝ)
    · have hc' : pathCost ω r.bypass ∈ C :=
        ⟨r.bypass, r.bypass_isPath, (bypass_cost_le ω hw r).trans hr, rfl⟩
      exact (hmin _ hc').trans (bypass_cost_le ω hw r)
    · exact hpm.trans (le_of_lt (lt_of_not_ge hr))
  refine ⟨p,hp,le_antisymm ?_ (passageTime_le_pathCost ω hw p)⟩
  apply le_csInf (s := Set.range (fun r : lattice.Walk x y => pathCost ω r)) ⟨_, ⟨p,rfl⟩⟩
  rintro _ ⟨r,rfl⟩
  exact hleast r

theorem geodesics_exist : ∀ᵐ ω ∂environmentLaw, ∀ x y : Vertex,
    ∃ p : lattice.Walk x y, p.IsPath ∧ pathCost ω p = passageTime ω x y := by
  filter_upwards [all_edge_weights_positive, bounded_cost_path_lengths] with ω hw hb
  intro x y
  exact exists_geodesic_of_bounded_cost ω (fun e => (hw e).le) x y (hb x)

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_CoordinatePath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP

theorem horizontal_length (a b : ℤ) (n : ℕ) :
    ∃ p : lattice.Walk (a, b) (a + (n : ℤ), b), p.length = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨p,hp⟩ := ih
    have h : lattice.Adj (a + (n : ℤ), b) (a + ((n+1 : ℕ) : ℤ), b) := by
      change |a + (n : ℤ) - (a + ((n+1 : ℕ) : ℤ))| + |b - b| = 1
      simp
    exact ⟨p.concat h, by simp [hp]⟩

theorem vertical_length (a b : ℤ) (n : ℕ) :
    ∃ p : lattice.Walk (a, b) (a, b + (n : ℤ)), p.length = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨p,hp⟩ := ih
    have h : lattice.Adj (a, b + (n : ℤ)) (a, b + ((n+1 : ℕ) : ℤ)) := by
      change |a - a| + |b + (n : ℤ) - (b + ((n+1 : ℕ) : ℤ))| = 1
      simp
    exact ⟨p.concat h, by simp [hp]⟩

theorem horizontal_coordinate_length (a c b : ℤ) :
    ∃ p : lattice.Walk (a,b) (c,b), p.length = (c-a).natAbs := by
  by_cases h : a ≤ c
  · have he : a + ((c-a).toNat : ℤ) = c := by omega
    have hn : (c-a).toNat = (c-a).natAbs := by omega
    have hh := horizontal_length a b (c-a).toNat
    rw [he] at hh
    simpa only [hn] using hh
  · have he : c + ((a-c).toNat : ℤ) = a := by omega
    obtain ⟨p,hp⟩ := horizontal_length c b (a-c).toNat
    have hn : (a-c).toNat = (c-a).natAbs := by omega
    have hq : ∃ p : lattice.Walk (c,b) (a,b), p.length = (c-a).natAbs := by
      have hh : ∃ p : lattice.Walk (c,b) (c + ((a-c).toNat : ℤ),b),
          p.length = (a-c).toNat := ⟨p,hp⟩
      rw [he] at hh
      simpa only [hn] using hh
    obtain ⟨q,hq⟩ := hq
    exact ⟨q.reverse, by simpa using hq⟩

theorem vertical_coordinate_length (a b c : ℤ) :
    ∃ p : lattice.Walk (a,b) (a,c), p.length = (c-b).natAbs := by
  by_cases h : b ≤ c
  · have he : b + ((c-b).toNat : ℤ) = c := by omega
    have hn : (c-b).toNat = (c-b).natAbs := by omega
    have hh := vertical_length a b (c-b).toNat
    rw [he] at hh
    simpa only [hn] using hh
  · have he : c + ((b-c).toNat : ℤ) = b := by omega
    have hn : (b-c).toNat = (c-b).natAbs := by omega
    have hq : ∃ p : lattice.Walk (a,c) (a,b), p.length = (c-b).natAbs := by
      have hh := vertical_length a c (b-c).toNat
      rw [he] at hh
      simpa only [hn] using hh
    obtain ⟨q,hq⟩ := hq
    exact ⟨q.reverse, by simpa using hq⟩

def latticeDistance (x y : Vertex) : ℕ := (y.1-x.1).natAbs + (y.2-x.2).natAbs

theorem coordinate_path (x y : Vertex) :
    ∃ p : lattice.Walk x y, p.IsPath ∧ p.length ≤ latticeDistance x y := by
  classical
  obtain ⟨p,hp⟩ := horizontal_coordinate_length x.1 y.1 x.2
  obtain ⟨q,hq⟩ := vertical_coordinate_length y.1 x.2 y.2
  refine ⟨(p.append q).bypass, (p.append q).bypass_isPath, ?_⟩
  exact (p.append q).length_bypass_le_length.trans (by simp [hp, hq, latticeDistance])

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_PositiveMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

lemma positive_weighted_density (x : ℝ) :
    exponentialPDF 1 x * ENNReal.ofReal (exp (x / 2)) =
      ENNReal.ofReal (2 : ℝ) * exponentialPDF (1 / 2) x := by
  by_cases hx : 0 ≤ x
  · rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hx]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    simp only [one_mul]
    calc
      exp (-x) * exp (x / 2) = exp (-(1 / 2 * x)) := by
        rw [← exp_add]
        congr 1
        ring
      _ = 2 * (1 / 2 * exp (-(1 / 2 * x))) := by ring
  · rw [exponentialPDF_of_neg (lt_of_not_ge hx),
      exponentialPDF_of_neg (lt_of_not_ge hx)]
    simp

theorem exponential_moment_half :
    (∫⁻ x, ENNReal.ofReal (exp (x / 2)) ∂expMeasure 1) = 2 := by
  change (∫⁻ x, ENNReal.ofReal (exp (x / 2)) ∂volume.withDensity (exponentialPDF 1)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume (by
    unfold exponentialPDF; fun_prop) (by fun_prop)]
  simp only [Pi.mul_apply, positive_weighted_density]
  rw [lintegral_const_mul _ (by unfold exponentialPDF; fun_prop),
    lintegral_exponentialPDF_eq_one (by norm_num : (0 : ℝ) < 1 / 2), mul_one]
  norm_num

theorem edge_set_positive_moment (s : Finset Edge) :
    (∫⁻ ω : Environment, ∏ e ∈ s, ENNReal.ofReal (exp (ω e / 2)) ∂environmentLaw) =
      2 ^ s.card := by
  have hind : iIndepFun (fun e (ω : Environment) => ENNReal.ofReal (exp (ω e / 2)))
      environmentLaw := iIndepFun_infinitePi (X := fun _ (x : ℝ) =>
        ENNReal.ofReal (exp (x / 2))) (by intro i; fun_prop)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun s _ hind (by intro i; fun_prop)]
  have he : ∀ e : Edge, (∫⁻ ω : Environment, ENNReal.ofReal (exp (ω e / 2))
      ∂environmentLaw) = 2 := by
    intro e
    rw [← lintegral_map (by fun_prop : Measurable (fun x : ℝ =>
      ENNReal.ofReal (exp (x / 2)))) (measurable_pi_apply e), edge_marginal]
    exact exponential_moment_half
  simp only [he, prod_const]

lemma positive_exp_sum (s : Finset Edge) (ω : Environment) :
    ENNReal.ofReal (exp ((∑ e ∈ s, ω e) / 2)) =
      ∏ e ∈ s, ENNReal.ofReal (exp (ω e / 2)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s he ih =>
    rw [sum_insert he, prod_insert he, add_div, exp_add,
      ENNReal.ofReal_mul (exp_pos _).le, ih]

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_PassageRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

@[fun_prop] theorem measurable_pathCost {x y : Vertex} (p : lattice.Walk x y) :
    Measurable (fun ω : Environment => pathCost ω p) := by
  induction p with
  | nil => exact measurable_const
  | cons h p ih => exact (measurable_pi_apply _).add ih

instance countable_lattice_walk (x y : Vertex) : Countable (lattice.Walk x y) :=
  Function.Injective.countable (f := fun p : lattice.Walk x y => p.support)
    (fun _ _ h => SimpleGraph.Walk.ext_support h)

@[fun_prop] theorem measurable_passageTime (x y : Vertex) :
    Measurable (fun ω : Environment => passageTime ω x y) := by
  exact Measurable.iInf (fun p : lattice.Walk x y => measurable_pathCost p)

theorem trail_positive_moment {x y : Vertex} (p : lattice.Walk x y) (hp : p.IsTrail) :
    (∫⁻ ω : Environment, ENNReal.ofReal (exp (pathCost ω p / 2)) ∂environmentLaw) =
      2 ^ p.length := by
  classical
  have hn := pathEdges_nodup hp
  have hc : (pathEdges p).toFinset.card = p.length := by
    rw [List.toFinset_card_of_nodup hn, pathEdges_length]
  have he : ∀ ω : Environment, (∑ e ∈ (pathEdges p).toFinset, ω e) = pathCost ω p := by
    intro ω
    rw [pathCost_eq_edgeList_sum]
    exact List.sum_toFinset _ hn
  have h := edge_set_positive_moment (pathEdges p).toFinset
  simp_rw [← positive_exp_sum, he, hc] at h
  exact h

theorem passageTime_positive_moment (x y : Vertex) :
    (∫⁻ ω : Environment, ENNReal.ofReal (exp (passageTime ω x y / 2)) ∂environmentLaw) ≤
      2 ^ latticeDistance x y := by
  obtain ⟨p,hp,hl⟩ := coordinate_path x y
  calc
    _ ≤ ∫⁻ ω : Environment, ENNReal.ofReal (exp (pathCost ω p / 2)) ∂environmentLaw := by
      apply lintegral_mono_ae
      filter_upwards [all_edge_weights_positive] with ω hω
      apply ENNReal.ofReal_le_ofReal
      apply exp_le_exp.mpr
      exact div_le_div_of_nonneg_right (passageTime_le_pathCost ω (fun e => (hω e).le) p)
        (by norm_num)
    _ = 2 ^ p.length := trail_positive_moment p hp.isTrail
    _ ≤ _ := by gcongr; norm_num

theorem integrable_exp_passageTime (x y : Vertex) :
    Integrable (fun ω : Environment => exp (passageTime ω x y / 2)) environmentLaw := by
  apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (by filter_upwards [] with ω; positivity)).mp
  exact ne_of_lt ((passageTime_positive_moment x y).trans_lt (by finiteness))

theorem integrable_passageTime (x y : Vertex) :
    Integrable (fun ω : Environment => passageTime ω x y) environmentLaw := by
  apply ((integrable_exp_passageTime x y).const_mul 2).mono'
    (measurable_passageTime x y).aestronglyMeasurable
  filter_upwards [all_edge_weights_positive] with ω hω
  have hn := passageTime_nonneg ω (fun e => (hω e).le) (lattice_walk x y)
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  have he := add_one_le_exp (passageTime ω x y / 2)
  linarith

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_LocalPassage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory Finset Real

noncomputable def localCandidates (x : Vertex) (R : ℕ) :
    Finset (Σ y : Vertex, lattice.Walk x y) := by
  classical
  exact ((range R).biUnion fun n => startingWalks n x).filter
    fun q => q.2.IsPath ∧ q.2.length < R

noncomputable def localEdges (x : Vertex) (R : ℕ) : Finset Edge := by
  classical
  exact (localCandidates x R).biUnion fun q => (pathEdges q.2).toFinset

noncomputable def localPassageTime (ω : Environment) (x y : Vertex) (R : ℕ) : ℝ :=
  sInf {c : ℝ | ∃ p : lattice.Walk x y, p.IsPath ∧ p.length < R ∧ c = pathCost ω p}

@[fun_prop] theorem measurable_localPassageTime (x y : Vertex) (R : ℕ) :
    Measurable (fun ω : Environment => localPassageTime ω x y R) := by
  have he : (fun ω : Environment => localPassageTime ω x y R) =
      (fun ω : Environment => ⨅ p : {p : lattice.Walk x y // p.IsPath ∧ p.length < R},
        pathCost ω p.1) := by
    funext ω
    unfold localPassageTime iInf
    congr 1
    ext c
    constructor
    · rintro ⟨p,hp,hl,rfl⟩
      exact ⟨⟨p,hp,hl⟩,rfl⟩
    · rintro ⟨⟨p,hp,hl⟩,rfl⟩
      exact ⟨p,hp,hl,rfl⟩
  rw [he]
  exact Measurable.iInf (fun p => measurable_pathCost p.1)

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_Stationarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory

def latticeTranslation (a : Vertex) : lattice ≃g lattice where
  toEquiv := Equiv.addLeft a
  map_rel_iff' := by
    intro x y
    change |(a.1+x.1)-(a.1+y.1)| + |(a.2+x.2)-(a.2+y.2)| = 1 ↔
      |x.1-y.1| + |x.2-y.2| = 1
    simp only [add_sub_add_left_eq_sub]

@[simp] lemma latticeTranslation_apply (a x : Vertex) : latticeTranslation a x = a+x := rfl

def environmentTranslation (a : Vertex) (ω : Environment) : Environment :=
  fun e => ω ((latticeTranslation a).mapEdgeSet e)

@[fun_prop] theorem measurable_environmentTranslation (a : Vertex) :
    Measurable (environmentTranslation a) := by
  unfold environmentTranslation
  fun_prop

theorem environmentTranslation_preserving (a : Vertex) :
    MeasurePreserving (environmentTranslation a) environmentLaw environmentLaw := by
  refine ⟨measurable_environmentTranslation a, ?_⟩
  have h := Measure.infinitePi_map_piCongrLeft (fun _ : Edge => expMeasure 1)
    (latticeTranslation a).mapEdgeSet.symm
  have he : (MeasurableEquiv.piCongrLeft (fun _ : Edge => ℝ)
      (latticeTranslation a).mapEdgeSet.symm : Environment → Environment) =
      environmentTranslation a := by
    funext ω e
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, environmentTranslation]
  rw [he] at h
  exact h

lemma pathCost_map_translation (a : Vertex) (ω : Environment) {x y : Vertex}
    (p : lattice.Walk x y) :
    pathCost ω (p.map (latticeTranslation a).toHom) =
      pathCost (environmentTranslation a ω) p := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [SimpleGraph.Walk.map_cons, pathCost_cons, ih]
    rfl

lemma walk_map_iso_surjective {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (x y : V) :
    Function.Surjective (fun p : G.Walk x y => p.map f.toHom) := by
  intro q
  let p := (q.map f.symm.toHom).copy (f.symm_apply_apply x) (f.symm_apply_apply y)
  refine ⟨p, ?_⟩
  apply SimpleGraph.Walk.ext_support
  simp only [p, SimpleGraph.Walk.support_map, SimpleGraph.Walk.support_copy, List.map_map]
  have he : (⇑f.toHom ∘ ⇑f.symm.toHom) = id := by
    funext v
    exact f.apply_symm_apply v
  simp only [he, List.map_id_fun, id_eq]

theorem passageTime_translation (a : Vertex) (ω : Environment) (x y : Vertex) :
    passageTime ω (a+x) (a+y) = passageTime (environmentTranslation a ω) x y := by
  unfold passageTime
  congr 1
  ext c
  constructor
  · rintro ⟨q,rfl⟩
    obtain ⟨p,rfl⟩ := walk_map_iso_surjective (latticeTranslation a) x y q
    exact ⟨p,(pathCost_map_translation a ω p).symm⟩
  · rintro ⟨p,rfl⟩
    exact ⟨p.map (latticeTranslation a).toHom, pathCost_map_translation a ω p⟩

theorem mean_passageTime_translation (a x y : Vertex) :
    (∫ ω : Environment, passageTime ω (a+x) (a+y) ∂environmentLaw) =
      ∫ ω : Environment, passageTime ω x y ∂environmentLaw := by
  simp_rw [passageTime_translation]
  have hm := integral_map (μ := environmentLaw) (measurable_environmentTranslation a).aemeasurable
    (measurable_passageTime x y).aestronglyMeasurable
  rw [(environmentTranslation_preserving a).map_eq] at hm
  exact hm.symm

theorem mean_passageTime_subadditive (x y : Vertex) :
    (∫ ω : Environment, passageTime ω 0 (x+y) ∂environmentLaw) ≤
      (∫ ω : Environment, passageTime ω 0 x ∂environmentLaw) +
      (∫ ω : Environment, passageTime ω 0 y ∂environmentLaw) := by
  have hb := integral_mono_ae (integrable_passageTime 0 (x+y))
    ((integrable_passageTime 0 x).add (integrable_passageTime x (x+y)))
    (by
      filter_upwards [passageTime_properties] with ω hω
      exact hω.2.2.2 0 x (x+y))
  simp only [Pi.add_apply] at hb
  rw [integral_add (integrable_passageTime 0 x) (integrable_passageTime x (x+y))] at hb
  have ht := mean_passageTime_translation x 0 y
  simp only [add_zero] at ht
  rw [ht] at hb
  exact hb

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_LocalSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory

noncomputable instance encodable_lattice_walk (x y : Vertex) : Encodable (lattice.Walk x y) :=
  Encodable.ofCountable _

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_LocalCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory

lemma environmentTranslation_add (a b : Vertex) (ω : Environment) :
    environmentTranslation a (environmentTranslation b ω) =
      environmentTranslation (b+a) ω := by
  funext e
  unfold environmentTranslation
  congr 1
  apply Subtype.ext
  change Sym2.map (fun x : Vertex => b+x) (Sym2.map (fun x : Vertex => a+x) e.val) =
    Sym2.map (fun x : Vertex => (b+a)+x) e.val
  rw [Sym2.map_map]
  congr 1
  funext x
  simp only [Function.comp_apply, add_assoc]

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_HilbertWeakCompactness
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open Topology Filter Metric Bornology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma hilbert_bidual_surjective : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ H) := by
  intro F
  let g : StrongDual ℝ H := F.comp (InnerProductSpace.toDual ℝ H).toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨(InnerProductSpace.toDual ℝ H).symm g, ?_⟩
  ext l
  obtain ⟨y, rfl⟩ := (InnerProductSpace.toDual ℝ H).surjective l
  change inner ℝ y ((InnerProductSpace.toDual ℝ H).symm g) = g y
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]

omit [CompleteSpace H] in

lemma isClosed_weakImage {s : Set H} (hc : Convex ℝ s) (hs : IsClosed s) :
    IsClosed (toWeakSpace ℝ H '' s) := by
  rw [← closure_eq_iff_isClosed, ← hc.toWeakSpace_closure ℝ, hs.closure_eq]

theorem hilbert_isCompact_weak_closedBall (r : ℝ) :
    IsCompact (toWeakSpace ℝ H '' closedBall (0 : H) r) := by
  have hc := NormedSpace.isCompact_closure_of_isBounded ℝ H
    (toWeakSpace ℝ H '' closedBall (0 : H) r) (by
      simpa only [Set.preimage_image_eq _ (toWeakSpace ℝ H).injective] using
        (isBounded_closedBall (x := (0 : H)) (r := r))) (by
      intro x _
      obtain ⟨y, hy⟩ := hilbert_bidual_surjective (H := H) (WeakDual.toStrongDual x)
      refine ⟨toWeakSpace ℝ H y, ?_⟩
      exact hy)
  rwa [(isClosed_weakImage (convex_closedBall (0 : H) r) isClosed_closedBall).closure_eq] at hc

theorem exists_weak_product_limit {I : Type*} (f : ℕ → I → H) (R : I → ℝ)
    (hb : ∀ n i, ‖f n i‖ ≤ R i) :
    ∃ (u : I → WeakSpace ℝ H) (l : Filter ℕ), l.NeBot ∧ l ≤ atTop ∧
      Tendsto (fun n i => toWeakSpace ℝ H (f n i)) l (𝓝 u) := by
  have hc : IsCompact {x : I → WeakSpace ℝ H | ∀ i, x i ∈ toWeakSpace ℝ H '' closedBall (0 : H) (R i)} :=
    isCompact_pi_infinite (fun i => hilbert_isCompact_weak_closedBall (H := H) (R i))
  obtain ⟨u, _, hu⟩ := hc.exists_mapClusterPt (f := atTop)
    (u := fun n i => toWeakSpace ℝ H (f n i)) (le_principal_iff.mpr (by
      change ∀ᶠ n : ℕ in atTop, ∀ i, toWeakSpace ℝ H (f n i) ∈ _
      exact Eventually.of_forall (fun n i => ⟨f n i, mem_closedBall_zero_iff.mpr (hb n i), rfl⟩)))
  exact ⟨u, atTop ⊓ comap (fun n i => toWeakSpace ℝ H (f n i)) (𝓝 u),
    (by simpa only [MapClusterPt, ClusterPt, ← Filter.push_pull', map_neBot_iff, inf_comm] using hu), inf_le_left, tendsto_iff_comap.mpr inf_le_right⟩

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_LatticeMetric
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory Real

lemma latticeDistance_triangle (x y z : Vertex) :
    latticeDistance x z ≤ latticeDistance x y + latticeDistance y z := by
  have h₁ := Int.natAbs_add_le (y.1-x.1) (z.1-y.1)
  have h₂ := Int.natAbs_add_le (y.2-x.2) (z.2-y.2)
  rw [show y.1-x.1+(z.1-y.1)=z.1-x.1 by ring] at h₁
  rw [show y.2-x.2+(z.2-y.2)=z.2-x.2 by ring] at h₂
  unfold latticeDistance
  omega

lemma latticeDistance_of_adj {x y : Vertex} (h : lattice.Adj x y) :
    latticeDistance x y = 1 := by
  change |x.1-y.1| + |x.2-y.2| = 1 at h
  have he : (latticeDistance x y : ℤ) = 1 := by
    simpa only [latticeDistance, Nat.cast_add, Int.natCast_natAbs, abs_sub_comm] using h
  exact_mod_cast he

theorem latticeDistance_le_length {x y : Vertex} (p : lattice.Walk x y) :
    latticeDistance x y ≤ p.length := by
  induction p with
  | nil => simp [latticeDistance]
  | @cons x y z h p ih =>
    have ht := latticeDistance_triangle x y z
    rw [latticeDistance_of_adj h] at ht
    simp only [SimpleGraph.Walk.length_cons]
    omega

theorem passageTime_lower_tail (x y : Vertex) (hd : 1 ≤ latticeDistance x y)
    (t : ℝ) (ht : 0 ≤ t) :
    environmentLaw.real {ω : Environment | passageTime ω x y ≤ t} ≤
      (8/3 : ℝ)*exp (5*t)*(1/2 : ℝ)^latticeDistance x y := by
  have hsub : environmentLaw {ω : Environment | passageTime ω x y ≤ t} ≤
      environmentLaw {ω : Environment | ∃ a ∈ ({x} : Finset Vertex), ∃ b,
        ∃ p : lattice.Walk a b, p.IsPath ∧ latticeDistance x y ≤ p.length ∧ pathCost ω p ≤ t} := by
    apply measure_mono_ae
    filter_upwards [geodesics_exist] with ω hω
    intro hcost
    obtain ⟨p,hp,hc⟩ := hω x y
    exact ⟨x,Finset.mem_singleton_self x,y,p,hp,latticeDistance_le_length p,hc ▸ hcost⟩
  apply (ENNReal.toReal_mono (measure_ne_top _ _) hsub).trans
  change environmentLaw.real _ ≤ _
  simpa only [Finset.card_singleton, Nat.cast_one, mul_one] using
    no_long_cheap_paths {x} (latticeDistance x y) hd t ht

theorem passageTime_small_linear_tail (x y : Vertex) (hd : 1 ≤ latticeDistance x y) :
    environmentLaw.real {ω : Environment |
      passageTime ω x y ≤ (log 2/10)*latticeDistance x y} ≤
      (8/3 : ℝ)*exp (-(log 2/2)*latticeDistance x y) := by
  apply (passageTime_lower_tail x y hd ((log 2/10)*latticeDistance x y) (by positivity)).trans_eq
  have hp : (1/2 : ℝ)^latticeDistance x y =
      exp (-((latticeDistance x y : ℝ)*log 2)) := by
    rw [exp_neg, exp_nat_mul, exp_log (by norm_num : (0 : ℝ) < 2)]
    simp [one_div]
  rw [hp, mul_assoc, ← exp_add]
  congr 2
  ring

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_MeanTimeConstant
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory Filter Topology

noncomputable def meanPassageSequence (x : Vertex) (n : ℕ) : ℝ :=
  ∫ ω : Environment, passageTime ω 0 (scaleVertex n x) ∂environmentLaw

lemma scaleVertex_add (m n : ℕ) (x : Vertex) :
    scaleVertex (m+n) x = scaleVertex m x + scaleVertex n x := by
  ext <;> simp [scaleVertex, add_mul]

lemma meanPassageSequence_nonneg (x : Vertex) (n : ℕ) :
    0 ≤ meanPassageSequence x n := by
  apply integral_nonneg_of_ae
  filter_upwards [passageTime_properties] with ω hω
  exact hω.1 _ _

theorem meanPassageSequence_subadditive (x : Vertex) :
    Subadditive (meanPassageSequence x) := by
  intro m n
  unfold meanPassageSequence
  rw [scaleVertex_add]
  exact mean_passageTime_subadditive (scaleVertex m x) (scaleVertex n x)

lemma meanPassageSequence_bddBelow (x : Vertex) :
    BddBelow (Set.range (fun n : ℕ => meanPassageSequence x n / n)) := by
  refine ⟨0, ?_⟩
  rintro r ⟨n,rfl⟩
  exact div_nonneg (meanPassageSequence_nonneg x n) (Nat.cast_nonneg _)

noncomputable def directionalMeanConstant (x : Vertex) : ℝ :=
  (meanPassageSequence_subadditive x).lim

theorem meanPassageSequence_tendsto (x : Vertex) :
    Tendsto (fun n : ℕ => meanPassageSequence x n / n) atTop (𝓝 (directionalMeanConstant x)) :=
  (meanPassageSequence_subadditive x).tendsto_lim (meanPassageSequence_bddBelow x)

theorem directionalMeanConstant_nonneg (x : Vertex) : 0 ≤ directionalMeanConstant x :=
  ge_of_tendsto (meanPassageSequence_tendsto x) (Filter.Eventually.of_forall
    (fun n => div_nonneg (meanPassageSequence_nonneg x n) (Nat.cast_nonneg _)))

theorem directionalMeanConstant_le_mean (x : Vertex) :
    directionalMeanConstant x ≤ ∫ ω : Environment, passageTime ω 0 x ∂environmentLaw := by
  have h := (meanPassageSequence_subadditive x).lim_le_div
    (meanPassageSequence_bddBelow x) (n := 1) (by norm_num)
  simpa [meanPassageSequence, directionalMeanConstant, scaleVertex] using h

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_MeanPositivity
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory Real Filter Topology

lemma passageTime_mean_lower_of_tail (x y : Vertex) (t b : ℝ) (ht : 0 ≤ t)
    (hb : environmentLaw.real {ω : Environment | passageTime ω x y ≤ t} ≤ b) :
    t*(1-b) ≤ ∫ ω : Environment, passageTime ω x y ∂environmentLaw := by
  classical
  let F := {ω : Environment | passageTime ω x y ≤ t}
  have hF : MeasurableSet F := measurableSet_le (measurable_passageTime x y) measurable_const
  have hi := integral_mono_ae ((integrable_const t).indicator hF.compl)
    (integrable_passageTime x y) (by
      filter_upwards [passageTime_properties] with ω hω
      by_cases hf : ω ∈ Fᶜ
      · rw [Set.indicator_of_mem hf]
        exact (lt_of_not_ge (show ¬ passageTime ω x y ≤ t from hf)).le
      · rw [Set.indicator_of_notMem hf]
        exact hω.1 x y)
  rw [integral_indicator_const t hF.compl] at hi
  have hu : environmentLaw.real Set.univ = 1 := by simp [measureReal_def]
  simp only [smul_eq_mul, measureReal_compl hF, hu] at hi
  have he : t*(1-b) ≤ (1-environmentLaw.real F)*t := by
    nlinarith
  exact he.trans hi

lemma small_tail_at_most_half (d : ℕ) (hd : 8 ≤ d) :
    (8/3 : ℝ)*exp (-(log 2/2)*d) ≤ 1/2 := by
  have hlog : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have he : exp (-(log 2/2)*d) ≤ exp (-((4 : ℕ)*log 2)) := by
    rw [exp_le_exp]
    norm_num
    nlinarith
  have hv : exp (-((4 : ℕ)*log (2 : ℝ))) = 1/16 := by
    rw [exp_neg, exp_nat_mul, exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hv] at he
  linarith

theorem passageTime_mean_linear_lower (x y : Vertex) (hd : 8 ≤ latticeDistance x y) :
    (log 2/20)*latticeDistance x y ≤
      ∫ ω : Environment, passageTime ω x y ∂environmentLaw := by
  have hb := (passageTime_small_linear_tail x y (by omega)).trans
    (small_tail_at_most_half (latticeDistance x y) hd)
  have hm := passageTime_mean_lower_of_tail x y ((log 2/10)*latticeDistance x y)
    (1/2) (by positivity) hb
  nlinarith

lemma latticeDistance_scaleVertex (n : ℕ) (x : Vertex) :
    latticeDistance 0 (scaleVertex n x) = n*latticeDistance 0 x := by
  simp [latticeDistance, scaleVertex, Int.natAbs_mul, Nat.mul_add]

theorem directionalMeanConstant_linear_lower (x : Vertex) :
    (log 2/20)*latticeDistance 0 x ≤ directionalMeanConstant x := by
  by_cases hx : latticeDistance 0 x = 0
  · simpa only [hx, Nat.cast_zero, mul_zero] using directionalMeanConstant_nonneg x
  have hd : 1 ≤ latticeDistance 0 x := by omega
  apply ge_of_tendsto (meanPassageSequence_tendsto x)
  filter_upwards [eventually_ge_atTop (8 : ℕ)] with n hn
  have hnd : 8 ≤ latticeDistance 0 (scaleVertex n x) := by
    rw [latticeDistance_scaleVertex]
    nlinarith
  have hm := passageTime_mean_linear_lower 0 (scaleVertex n x) hnd
  rw [latticeDistance_scaleVertex, Nat.cast_mul] at hm
  change (log 2/20)*((n : ℝ)*latticeDistance 0 x) ≤ meanPassageSequence x n at hm
  apply (le_div_iff₀ (by exact_mod_cast (show 0 < n by omega))).mpr
  nlinarith

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_NaturalMoment
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real

lemma exponential_nat_moment_density (n : ℕ) (x : ℝ) :
    exponentialPDF 1 x * ENNReal.ofReal (x^n) =
      ENNReal.ofReal (n.factorial : ℝ) * gammaPDF (n+1) 1 x := by
  by_cases hx : 0 ≤ x
  · rw [exponentialPDF_of_nonneg hx, gammaPDF_of_nonneg hx,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [one_mul, one_rpow, add_sub_cancel_right]
    rw [Real.rpow_natCast]
    rw [Real.Gamma_nat_eq_factorial]
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  · rw [exponentialPDF_of_neg (lt_of_not_ge hx), gammaPDF_of_neg (lt_of_not_ge hx)]
    simp

theorem exponential_nat_lmoment (n : ℕ) :
    (∫⁻ x, ENNReal.ofReal (x^n) ∂expMeasure 1) = n.factorial := by
  change (∫⁻ x, ENNReal.ofReal (x^n) ∂volume.withDensity (exponentialPDF 1)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume (by unfold exponentialPDF; fun_prop)
    (by fun_prop)]
  simp only [Pi.mul_apply, exponential_nat_moment_density]
  rw [lintegral_const_mul _ (by unfold gammaPDF; fun_prop),
    lintegral_gammaPDF_eq_one (by positivity) (by norm_num), mul_one]
  simp

theorem integrable_exponential_pow (n : ℕ) :
    Integrable (fun x : ℝ => x^n) (expMeasure 1) := by
  apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (by filter_upwards [exponential_positive] with x hx; positivity)).mp
  rw [exponential_nat_lmoment]
  finiteness

theorem integral_exponential_pow (n : ℕ) :
    (∫ x : ℝ, x^n ∂expMeasure 1) = n.factorial := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (by filter_upwards [exponential_positive] with x hx; positivity) (by fun_prop),
    exponential_nat_lmoment]
  simp

lemma integrable_edge_weight (e : Edge) :
    Integrable (fun ω : Environment => ω e) environmentLaw := by
  have h := (integrable_exponential_pow 1)
  simp only [pow_one] at h
  exact (measurePreserving_eval_infinitePi (fun _ : Edge => expMeasure 1) e).integrable_comp_of_integrable h

lemma integral_edge_weight (e : Edge) :
    (∫ ω : Environment, ω e ∂environmentLaw) = 1 := by
  have h := integral_map (μ := environmentLaw) (measurable_pi_apply e).aemeasurable
    (f := fun x : ℝ => x) (by fun_prop)
  rw [edge_marginal] at h
  have h1 : (∫ x : ℝ, x ∂expMeasure 1) = 1 := by
    simpa using integral_exponential_pow 1
  exact h.symm.trans h1

theorem integral_pathCost {x y : Vertex} (p : lattice.Walk x y) :
    Integrable (fun ω : Environment => pathCost ω p) environmentLaw ∧
      (∫ ω : Environment, pathCost ω p ∂environmentLaw) = p.length := by
  induction p with
  | nil => simp [pathCost_nil]
  | cons h p ih =>
    have he := integrable_edge_weight (⟨s(_, _), h⟩ : Edge)
    constructor
    · exact he.add ih.1
    · rw [show (fun ω : Environment => pathCost ω (.cons h p)) =
        (fun ω => ω (⟨s(_, _), h⟩ : Edge) + pathCost ω p) from rfl,
        integral_add he ih.1, integral_edge_weight, ih.2]
      simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      ring

theorem mean_passageTime_le_distance (x y : Vertex) :
    (∫ ω : Environment, passageTime ω x y ∂environmentLaw) ≤ latticeDistance x y := by
  obtain ⟨p,hp,hl⟩ := coordinate_path x y
  have h := integral_mono_ae (integrable_passageTime x y) (integral_pathCost p).1
    (by filter_upwards [all_edge_weights_positive] with ω hω
        exact passageTime_le_pathCost ω (fun e => (hω e).le) p)
  rw [(integral_pathCost p).2] at h
  exact h.trans (by exact_mod_cast hl)

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_MetricCalibration
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory Real Finset Filter Topology

noncomputable def targetCocycle (z : Vertex) (ω : Environment) (x y : Vertex) : ℝ :=
  passageTime ω x z - passageTime ω y z

@[fun_prop] theorem measurable_targetCocycle (z x y : Vertex) :
    Measurable (fun ω : Environment => targetCocycle z ω x y) :=
  (measurable_passageTime x z).sub (measurable_passageTime y z)

theorem integrable_targetCocycle (z x y : Vertex) :
    Integrable (fun ω : Environment => targetCocycle z ω x y) environmentLaw :=
  (integrable_passageTime x z).sub (integrable_passageTime y z)

theorem targetCocycle_dominated : ∀ᵐ ω ∂environmentLaw, ∀ z x y : Vertex,
    |targetCocycle z ω x y| ≤ passageTime ω x y := by
  filter_upwards [passageTime_properties] with ω hω
  intro z x y
  apply abs_le.mpr
  have h₁ := hω.2.2.2 x y z
  have h₂ := hω.2.2.2 y x z
  rw [hω.2.2.1 y x] at h₂
  unfold targetCocycle
  constructor <;> linarith

theorem targetCocycle_translation (a z x y : Vertex) (ω : Environment) :
    targetCocycle (a+z) ω (a+x) (a+y) =
      targetCocycle z (environmentTranslation a ω) x y := by
  simp only [targetCocycle, passageTime_translation]

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_CalibrationShift
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory Real Finset Filter Topology

lemma scaleVertex_succ (k : ℕ) (d : Vertex) :
    scaleVertex (k+1) d = d + scaleVertex k d := by
  rw [scaleVertex_add]
  simp [scaleVertex, add_comm]

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_FiniteProduct
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset

abbrev LocalCoordinates (x : Vertex) (R : ℕ) := (e : ↥(localEdges x R)) → ℝ

noncomputable def extendLocalCoordinates (x : Vertex) (R : ℕ)
    (v : LocalCoordinates x R) : Environment := by
  classical
  exact fun e => if he : e ∈ localEdges x R then v ⟨e,he⟩ else 0

@[simp] lemma extendLocalCoordinates_apply (x : Vertex) (R : ℕ)
    (v : LocalCoordinates x R) (e : ↥(localEdges x R)) :
    extendLocalCoordinates x R v e = v e := by
  classical
  simp [extendLocalCoordinates, e.property]

noncomputable def finitePassageTime (x y : Vertex) (R : ℕ)
    (v : LocalCoordinates x R) : ℝ := localPassageTime (extendLocalCoordinates x R v) x y R

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_ResamplingMoment
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

noncomputable def upwardResampling (ω : Environment) (x y : Vertex) (R : ℕ)
    (e : Edge) (u : ℝ) : ℝ := by
  classical
  exact max (localPassageTime (Function.update ω e u) x y R -
    localPassageTime ω x y R) 0

@[fun_prop] lemma measurable_upwardResampling (ω : Environment) (x y : Vertex)
    (R : ℕ) (e : Edge) : Measurable (upwardResampling ω x y R e) := by
  classical
  unfold upwardResampling
  fun_prop

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_FiniteVariance
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
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
-- module Solutions.OAIS_PlanarFPP.LatticePassage_ResamplingSymmetry
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
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
-- module Solutions.OAIS_PlanarFPP.LatticePassage_EfronStein
attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
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
-- module Solutions.OAIS_PlanarFPP.LatticePassage_CenteredLocalization
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory Real

lemma mean_passageTime_nonneg (x y : Vertex) :
    0 ≤ ∫ ω : Environment, passageTime ω x y ∂environmentLaw := by
  apply integral_nonneg_of_ae
  filter_upwards [passageTime_properties] with ω hω
  exact hω.1 x y

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_OffsetCalibration
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory Real Finset

lemma mean_passageTime_endpoint_lipschitz (s t : Vertex) :
    |(∫ ω, passageTime ω 0 s ∂environmentLaw) -
      (∫ ω, passageTime ω 0 t ∂environmentLaw)| ≤ (latticeDistance s t : ℝ) := by
  have he : (∫ ω, passageTime ω 0 s ∂environmentLaw) -
      (∫ ω, passageTime ω 0 t ∂environmentLaw) =
      ∫ ω, targetCocycle 0 ω s t ∂environmentLaw := by
    rw [← integral_sub (integrable_passageTime 0 s) (integrable_passageTime 0 t)]
    apply integral_congr_ae
    filter_upwards [passageTime_properties] with ω hω
    unfold targetCocycle
    rw [hω.2.2.1 s 0, hω.2.2.1 t 0]
  rw [he]
  have hnorm := norm_integral_le_integral_norm (μ := environmentLaw) (fun ω => targetCocycle 0 ω s t)
  simp only [Real.norm_eq_abs] at hnorm
  apply hnorm.trans
  apply (integral_mono_ae (integrable_targetCocycle 0 s t).abs (integrable_passageTime s t)
    (by filter_upwards [targetCocycle_dominated] with ω hω; exact hω 0 s t)).trans
  exact mean_passageTime_le_distance s t

noncomputable def offsetTargetCocycle (s d : Vertex) (N : ℕ)
    (ω : Environment) (x y : Vertex) : ℝ :=
  (∑ k ∈ range N, targetCocycle (s+scaleVertex (k+1) d) ω x y) / N

@[fun_prop] lemma measurable_offsetTargetCocycle (s d x y : Vertex) (N : ℕ) :
    Measurable (fun ω => offsetTargetCocycle s d N ω x y) := by
  unfold offsetTargetCocycle
  fun_prop

lemma integrable_offsetTargetCocycle (s d x y : Vertex) (N : ℕ) :
    Integrable (fun ω => offsetTargetCocycle s d N ω x y) environmentLaw :=
  (integrable_finsetSum _ (fun _k _ => integrable_targetCocycle _ _ _)).div_const _

lemma integral_offset_target_step (s d : Vertex) (k : ℕ) :
    (∫ ω, targetCocycle (s+scaleVertex (k+1) d) ω 0 d ∂environmentLaw) =
      (∫ ω, passageTime ω 0 (s+scaleVertex (k+1) d) ∂environmentLaw) -
      (∫ ω, passageTime ω 0 (s+scaleVertex k d) ∂environmentLaw) := by
  unfold targetCocycle
  rw [integral_sub (integrable_passageTime _ _) (integrable_passageTime _ _)]
  have he : s+scaleVertex (k+1) d = d+(s+scaleVertex k d) := by
    rw [scaleVertex_succ]
    abel
  have ht := mean_passageTime_translation d 0 (s+scaleVertex k d)
  simp only [add_zero] at ht
  rw [he, ht]

theorem integral_offsetTargetCocycle (s d : Vertex) (N : ℕ) :
    (∫ ω, offsetTargetCocycle s d N ω 0 d ∂environmentLaw) =
      ((∫ ω, passageTime ω 0 (s+scaleVertex N d) ∂environmentLaw) -
        (∫ ω, passageTime ω 0 s ∂environmentLaw)) / N := by
  unfold offsetTargetCocycle
  rw [integral_div, integral_finsetSum _ (fun _k _ => integrable_targetCocycle _ _ _)]
  simp_rw [integral_offset_target_step]
  rw [sum_range_sub (fun k => ∫ ω, passageTime ω 0 (s+scaleVertex k d) ∂environmentLaw)]
  have hz : scaleVertex 0 d = (0 : Vertex) := by ext <;> simp [scaleVertex]
  rw [hz, add_zero]

theorem offsetTargetCocycle_mean_error (s d : Vertex) (N : ℕ) :
    |(∫ ω, offsetTargetCocycle s d N ω 0 d ∂environmentLaw) -
      meanPassageSequence d N/N| ≤ 2*(latticeDistance 0 s : ℝ)/N := by
  rw [integral_offsetTargetCocycle, ← sub_div, abs_div,
    show |(N : ℝ)| = (N : ℝ) from abs_of_nonneg (Nat.cast_nonneg N)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  have h₁ := mean_passageTime_endpoint_lipschitz (s+scaleVertex N d) (scaleVertex N d)
  have hdist : latticeDistance (s+scaleVertex N d) (scaleVertex N d) = latticeDistance 0 s := by
    simp [latticeDistance]
  rw [hdist] at h₁
  have h₂ := mean_passageTime_le_distance 0 s
  have h₃ := mean_passageTime_nonneg 0 s
  have htri := abs_sub ((∫ ω, passageTime ω 0 (s+scaleVertex N d) ∂environmentLaw) -
    meanPassageSequence d N) (∫ ω, passageTime ω 0 s ∂environmentLaw)
  rw [abs_of_nonneg h₃] at htri
  change |(∫ ω, passageTime ω 0 (s+scaleVertex N d) ∂environmentLaw) -
    meanPassageSequence d N| ≤ _ at h₁
  have he : (∫ ω, passageTime ω 0 (s+scaleVertex N d) ∂environmentLaw) -
      (∫ ω, passageTime ω 0 s ∂environmentLaw) - meanPassageSequence d N =
      ((∫ ω, passageTime ω 0 (s+scaleVertex N d) ∂environmentLaw) - meanPassageSequence d N) -
      (∫ ω, passageTime ω 0 s ∂environmentLaw) := by ring
  rw [he]
  linarith

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_SecondMoment
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Finset

lemma integrable_edge_square (e : Edge) :
    Integrable (fun ω : Environment => (ω e)^2) environmentLaw :=
  (measurePreserving_eval_infinitePi (fun _ : Edge => expMeasure 1) e).integrable_comp_of_integrable
    (integrable_exponential_pow 2)

lemma edge_memLp_two (e : Edge) : MemLp (fun ω : Environment => ω e) 2 environmentLaw :=
  (memLp_two_iff_integrable_sq (measurable_pi_apply e).aestronglyMeasurable).mpr (integrable_edge_square e)

theorem pathCost_memLp_two {x y : Vertex} (p : lattice.Walk x y) :
    MemLp (fun ω : Environment => pathCost ω p) 2 environmentLaw := by
  induction p with
  | nil => exact memLp_const 0
  | cons h p ih => exact (edge_memLp_two (⟨s(_,_),h⟩ : Edge)).add ih

theorem passageTime_memLp_two (x y : Vertex) :
    MemLp (fun ω : Environment => passageTime ω x y) 2 environmentLaw := by
  obtain ⟨p,_,_⟩ := coordinate_path x y
  apply (pathCost_memLp_two p).mono' (by fun_prop)
  filter_upwards [all_edge_weights_positive] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (passageTime_nonneg ω (fun e => (hω e).le) (lattice_walk x y))]
  exact passageTime_le_pathCost ω (fun e => (hω e).le) p

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_RectangleCalibration
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory Real Finset Filter Topology

noncomputable def rectangleTargetCocycle (z a b : Vertex) (N M : ℕ)
    (ω : Environment) (x y : Vertex) : ℝ :=
  (∑ i ∈ range N, ∑ j ∈ range M,
    targetCocycle (z+scaleVertex i a+scaleVertex j b) ω x y) / ((N : ℝ)*M)

@[fun_prop] lemma measurable_rectangleTargetCocycle (z a b x y : Vertex) (N M : ℕ) :
    Measurable (fun ω => rectangleTargetCocycle z a b N M ω x y) := by
  unfold rectangleTargetCocycle
  fun_prop

theorem rectangleTargetCocycle_add (z a b : Vertex) (N M : ℕ)
    (ω : Environment) (x y w : Vertex) :
    rectangleTargetCocycle z a b N M ω x w =
      rectangleTargetCocycle z a b N M ω x y + rectangleTargetCocycle z a b N M ω y w := by
  unfold rectangleTargetCocycle
  simp only [targetCocycle, sum_sub_distrib]
  ring

lemma rectangleTargetCocycle_swap (z a b : Vertex) (N M : ℕ)
    (ω : Environment) (x y : Vertex) :
    rectangleTargetCocycle z a b N M ω x y = rectangleTargetCocycle z b a M N ω x y := by
  unfold rectangleTargetCocycle
  rw [sum_comm, mul_comm (N : ℝ)]
  congr 1
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro i _
  rw [show z+scaleVertex i a+scaleVertex j b = z+scaleVertex j b+scaleVertex i a by abel]

theorem rectangleTargetCocycle_dominated (z a b : Vertex) (N M : ℕ)
    (hN : 1 ≤ N) (hM : 1 ≤ M) :
    ∀ᵐ ω ∂environmentLaw, ∀ x y,
      |rectangleTargetCocycle z a b N M ω x y| ≤ passageTime ω x y := by
  filter_upwards [targetCocycle_dominated] with ω hω
  intro x y
  unfold rectangleTargetCocycle
  rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ (N : ℝ)*M)]
  have hb : |∑ i ∈ range N, ∑ j ∈ range M,
      targetCocycle (z+scaleVertex i a+scaleVertex j b) ω x y| ≤
      (N : ℝ)*M*passageTime ω x y := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ i ∈ range N, ∑ j ∈ range M, passageTime ω x y := by
        apply sum_le_sum
        intro i _
        exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun j _ => hω _ x y))
      _ = _ := by simp; ring
  have hp : 0 < (N : ℝ)*M := mul_pos (by exact_mod_cast hN) (by exact_mod_cast hM)
  exact (div_le_iff₀ hp).mpr (by simpa only [mul_comm (passageTime ω x y)] using hb)

theorem rectangleTargetCocycle_shift_identity (z a b : Vertex) (N M : ℕ)
    (ω : Environment) (x y : Vertex) :
    rectangleTargetCocycle z a b N M (environmentTranslation a ω) x y -
      rectangleTargetCocycle z a b N M ω (a+x) (a+y) =
    (∑ j ∈ range M,
      (targetCocycle (z+scaleVertex N a+scaleVertex j b) ω (a+x) (a+y) -
       targetCocycle (z+scaleVertex j b) ω (a+x) (a+y))) / ((N : ℝ)*M) := by
  unfold rectangleTargetCocycle
  rw [← sub_div, ← sum_sub_distrib]
  have he : ∀ i j : ℕ,
      targetCocycle (z+scaleVertex i a+scaleVertex j b) (environmentTranslation a ω) x y =
      targetCocycle (z+scaleVertex (i+1) a+scaleVertex j b) ω (a+x) (a+y) := by
    intro i j
    rw [← targetCocycle_translation]
    congr 1
    rw [scaleVertex_succ]
    abel
  simp only [he, ← sum_sub_distrib]
  rw [sum_comm]
  have htel (j : ℕ) := sum_range_sub
    (fun i : ℕ => targetCocycle (z+scaleVertex i a+scaleVertex j b) ω (a+x) (a+y)) N
  simp_rw [htel]
  have hz : scaleVertex 0 a = (0 : Vertex) := by ext <;> simp [scaleVertex]
  simp only [hz, add_zero]

theorem rectangleTargetCocycle_shift_bound (z a b : Vertex) (N M : ℕ)
    (hN : 1 ≤ N) (hM : 1 ≤ M) (x y : Vertex) :
    ∀ᵐ ω ∂environmentLaw,
      |rectangleTargetCocycle z a b N M (environmentTranslation a ω) x y -
        rectangleTargetCocycle z a b N M ω (a+x) (a+y)| ≤
      2*passageTime ω (a+x) (a+y)/N := by
  filter_upwards [targetCocycle_dominated] with ω hω
  rw [rectangleTargetCocycle_shift_identity, abs_div,
    abs_of_nonneg (by positivity : 0 ≤ (N : ℝ)*M)]
  have hb : |∑ j ∈ range M,
      (targetCocycle (z+scaleVertex N a+scaleVertex j b) ω (a+x) (a+y) -
       targetCocycle (z+scaleVertex j b) ω (a+x) (a+y))| ≤
      (M : ℝ)*(2*passageTime ω (a+x) (a+y)) := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ j ∈ range M, 2*passageTime ω (a+x) (a+y) := by
        apply sum_le_sum
        intro j _
        apply (abs_sub _ _).trans
        linarith [hω (z+scaleVertex N a+scaleVertex j b) (a+x) (a+y),
          hω (z+scaleVertex j b) (a+x) (a+y)]
      _ = _ := by simp
  apply (div_le_div_of_nonneg_right hb (by positivity)).trans_eq
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  field_simp

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_PlanarCalibration
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory Real Finset Filter Topology

lemma abs_range_average_le {f : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N) {B : ℝ}
    (h : ∀ k ∈ range N, |f k| ≤ B) : |(∑ k ∈ range N, f k) / N| ≤ B := by
  rw [abs_div, show |(N : ℝ)| = N from abs_of_nonneg (Nat.cast_nonneg N)]
  have hb : |∑ k ∈ range N, f k| ≤ (N : ℝ)*B :=
    (abs_sum_le_sum_abs _ _).trans (by simpa using sum_le_sum h)
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  exact (div_le_iff₀ hn).mpr (by simpa only [mul_comm B] using hb)

noncomputable def planarTargetCocycle (d a b : Vertex) (N M : ℕ)
    (ω : Environment) (x y : Vertex) : ℝ :=
  (∑ k ∈ range N, rectangleTargetCocycle (scaleVertex (k+1) d) a b M M ω x y) / N

@[fun_prop] lemma measurable_planarTargetCocycle (d a b x y : Vertex) (N M : ℕ) :
    Measurable (fun ω => planarTargetCocycle d a b N M ω x y) := by
  unfold planarTargetCocycle
  fun_prop

theorem planarTargetCocycle_add (d a b : Vertex) (N M : ℕ)
    (ω : Environment) (x y z : Vertex) :
    planarTargetCocycle d a b N M ω x z =
      planarTargetCocycle d a b N M ω x y + planarTargetCocycle d a b N M ω y z := by
  unfold planarTargetCocycle
  simp_rw [rectangleTargetCocycle_add _ _ _ _ _ _ x y z]
  rw [sum_add_distrib, add_div]

theorem planarTargetCocycle_dominated (d a b : Vertex) (N M : ℕ)
    (hN : 1 ≤ N) (hM : 1 ≤ M) :
    ∀ᵐ ω ∂environmentLaw, ∀ x y,
      |planarTargetCocycle d a b N M ω x y| ≤ passageTime ω x y := by
  have hall : ∀ᵐ ω ∂environmentLaw, ∀ k : ℕ, ∀ x y,
      |rectangleTargetCocycle (scaleVertex (k+1) d) a b M M ω x y| ≤ passageTime ω x y :=
    ae_all_iff.mpr (fun k => rectangleTargetCocycle_dominated _ _ _ _ _ hM hM)
  filter_upwards [hall] with ω hω
  intro x y
  exact abs_range_average_le hN (fun k _ => hω k x y)

theorem planarTargetCocycle_memLp_two (d a b x y : Vertex) (N M : ℕ)
    (hN : 1 ≤ N) (hM : 1 ≤ M) :
    MemLp (fun ω => planarTargetCocycle d a b N M ω x y) 2 environmentLaw := by
  apply (passageTime_memLp_two x y).mono' (by fun_prop)
  filter_upwards [planarTargetCocycle_dominated d a b N M hN hM] with ω hω
  simpa only [Real.norm_eq_abs] using hω x y

theorem planarTargetCocycle_swap (d a b : Vertex) (N M : ℕ)
    (ω : Environment) (x y : Vertex) :
    planarTargetCocycle d a b N M ω x y = planarTargetCocycle d b a N M ω x y := by
  simp only [planarTargetCocycle, rectangleTargetCocycle_swap _ a b]

theorem planarTargetCocycle_shift_bound (d a b x y : Vertex) (N M : ℕ)
    (hN : 1 ≤ N) (hM : 1 ≤ M) :
    ∀ᵐ ω ∂environmentLaw,
      |planarTargetCocycle d a b N M (environmentTranslation a ω) x y -
        planarTargetCocycle d a b N M ω (a+x) (a+y)| ≤
      2*passageTime ω (a+x) (a+y)/M := by
  have hall : ∀ᵐ ω ∂environmentLaw, ∀ k : ℕ,
      |rectangleTargetCocycle (scaleVertex (k+1) d) a b M M (environmentTranslation a ω) x y -
        rectangleTargetCocycle (scaleVertex (k+1) d) a b M M ω (a+x) (a+y)| ≤
      2*passageTime ω (a+x) (a+y)/M :=
    ae_all_iff.mpr (fun k => rectangleTargetCocycle_shift_bound _ _ _ _ _ hM hM x y)
  filter_upwards [hall] with ω hω
  simp only [planarTargetCocycle, ← sub_div, ← sum_sub_distrib]
  exact abs_range_average_le hN (fun k _ => hω k)

theorem planarTargetCocycle_eq_offsets (d a b : Vertex) (N M : ℕ)
    (ω : Environment) (x y : Vertex) :
    planarTargetCocycle d a b N M ω x y =
      (∑ i ∈ range M, ∑ j ∈ range M,
        offsetTargetCocycle (scaleVertex i a+scaleVertex j b) d N ω x y) / ((M : ℝ)*M) := by
  unfold planarTargetCocycle rectangleTargetCocycle offsetTargetCocycle
  simp only [← sum_div]
  rw [sum_comm (s := range N), sum_congr rfl (fun i _ => sum_comm (s := range N))]
  have he : ∀ k i j : ℕ,
      scaleVertex (k+1) d+scaleVertex i a+scaleVertex j b =
      scaleVertex i a+scaleVertex j b+scaleVertex (k+1) d := by intros; abel
  simp only [he]
  ring

theorem planarTargetCocycle_mean_error (d a b : Vertex) (N M : ℕ) (hM : 1 ≤ M)
    (K : ℝ) (hK : ∀ i ∈ range M, ∀ j ∈ range M,
      (latticeDistance 0 (scaleVertex i a+scaleVertex j b) : ℝ) ≤ K) :
    |(∫ ω, planarTargetCocycle d a b N M ω 0 d ∂environmentLaw) -
      meanPassageSequence d N/N| ≤ 2*K/N := by
  simp_rw [planarTargetCocycle_eq_offsets]
  rw [integral_div, integral_finsetSum _ (fun _ _ => integrable_finsetSum _
    (fun _ _ => integrable_offsetTargetCocycle _ _ _ _ _))]
  simp_rw [integral_finsetSum _ (fun _ _ => integrable_offsetTargetCocycle _ _ _ _ _)]
  have hn : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have he (c : ℝ) :
      (∑ i ∈ range M, ∑ j ∈ range M,
        ((∫ ω, offsetTargetCocycle (scaleVertex i a+scaleVertex j b) d N ω 0 d ∂environmentLaw)-c)) /
          ((M : ℝ)*M) =
      (∑ i ∈ range M, ∑ j ∈ range M,
        ∫ ω, offsetTargetCocycle (scaleVertex i a+scaleVertex j b) d N ω 0 d ∂environmentLaw) /
          ((M : ℝ)*M)-c := by
    simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    field_simp
  rw [← he]
  have he' : ∀ f : ℕ → ℕ → ℝ,
      (∑ i ∈ range M, ∑ j ∈ range M, f i j) / ((M : ℝ)*M) =
      (∑ i ∈ range M, (∑ j ∈ range M, f i j)/M)/M := by
    intro f; rw [← sum_div, div_div]
  rw [he']
  apply abs_range_average_le hM
  intro i hi
  apply abs_range_average_le hM
  intro j hj
  exact (offsetTargetCocycle_mean_error _ d N).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hK i hi j hj) (by norm_num))
      (Nat.cast_nonneg N))

lemma latticeDistance_planar_offset_le (a b : Vertex) (M i j : ℕ)
    (hi : i ∈ range M) (hj : j ∈ range M) :
    (latticeDistance 0 (scaleVertex i a+scaleVertex j b) : ℝ) ≤
      (M : ℝ)*((latticeDistance 0 a : ℝ)+latticeDistance 0 b) := by
  have ht := latticeDistance_triangle 0 (scaleVertex i a) (scaleVertex i a+scaleVertex j b)
  have he : latticeDistance (scaleVertex i a) (scaleVertex i a+scaleVertex j b) =
      latticeDistance 0 (scaleVertex j b) := by simp [latticeDistance]
  rw [he, latticeDistance_scaleVertex, latticeDistance_scaleVertex] at ht
  have hb : i*latticeDistance 0 a+j*latticeDistance 0 b ≤
      M*latticeDistance 0 a+M*latticeDistance 0 b :=
    Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.le_of_lt (mem_range.mp hi)))
      (Nat.mul_le_mul_right _ (Nat.le_of_lt (mem_range.mp hj)))
  have hc := ht.trans hb
  exact_mod_cast (by simpa only [Nat.mul_add] using hc)

noncomputable def calibrationApprox (d a b : Vertex) (n : ℕ)
    (ω : Environment) (x y : Vertex) : ℝ :=
  planarTargetCocycle d a b ((n+1)*(n+1)) (n+1) ω x y

theorem calibrationApprox_mean_error (d a b : Vertex) (n : ℕ) :
    |(∫ ω, calibrationApprox d a b n ω 0 d ∂environmentLaw) -
      meanPassageSequence d ((n+1)*(n+1))/((n+1)*(n+1))| ≤
      (2*((latticeDistance 0 a : ℝ)+latticeDistance 0 b))/(n+1) := by
  have h := planarTargetCocycle_mean_error d a b ((n+1)*(n+1)) (n+1) (by omega)
    ((n+1)*((latticeDistance 0 a : ℝ)+latticeDistance 0 b))
    (by
      intro i hi j hj
      simpa only [Nat.cast_add, Nat.cast_one] using latticeDistance_planar_offset_le a b (n+1) i j hi hj)
  convert h using 1 <;> push_cast <;> try rfl
  field_simp

theorem calibrationApprox_mean_tendsto (d a b : Vertex) :
    Tendsto (fun n : ℕ => ∫ ω, calibrationApprox d a b n ω 0 d ∂environmentLaw)
      atTop (𝓝 (directionalMeanConstant d)) := by
  have hn : Tendsto (fun n : ℕ => n+1) atTop atTop := tendsto_add_atTop_nat 1
  have hs : Tendsto (fun n : ℕ => (n+1)*(n+1)) atTop atTop :=
    tendsto_atTop_mono (fun n => by nlinarith : ∀ n : ℕ, n+1 ≤ (n+1)*(n+1)) hn
  have hmean := (meanPassageSequence_tendsto d).comp hs
  have herr := (tendsto_const_div_atTop_nhds_zero_nat
    (2*((latticeDistance 0 a : ℝ)+latticeDistance 0 b))).comp hn
  have hz : Tendsto (fun n : ℕ =>
      (∫ ω, calibrationApprox d a b n ω 0 d ∂environmentLaw) -
      meanPassageSequence d ((n+1)*(n+1))/((n+1)*(n+1))) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) (by simpa only [Nat.cast_add, Nat.cast_one] using herr)
    simpa only [Real.norm_eq_abs, Function.comp_apply, Nat.cast_add, Nat.cast_one] using calibrationApprox_mean_error d a b n
  have ht := hz.add hmean
  simpa only [Function.comp_apply, Nat.cast_mul, Nat.cast_add, Nat.cast_one, sub_add_cancel, zero_add] using ht

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_CalibrationL2
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory Real Filter Topology

noncomputable abbrev CalibrationL2 := Lp ℝ 2 environmentLaw

noncomputable def passageL2 (x y : Vertex) : CalibrationL2 :=
  (passageTime_memLp_two x y).toLp (fun ω => passageTime ω x y)

noncomputable def approxL2 (d a b : Vertex) (n : ℕ) (x y : Vertex) : CalibrationL2 :=
  (planarTargetCocycle_memLp_two d a b x y ((n+1)*(n+1)) (n+1)
    (by nlinarith) (by omega)).toLp (fun ω => calibrationApprox d a b n ω x y)

lemma coe_passageL2 (x y : Vertex) : passageL2 x y =ᵐ[environmentLaw] fun ω => passageTime ω x y :=
  MemLp.coeFn_toLp _

lemma coe_approxL2 (d a b : Vertex) (n : ℕ) (x y : Vertex) :
    approxL2 d a b n x y =ᵐ[environmentLaw] fun ω => calibrationApprox d a b n ω x y :=
  MemLp.coeFn_toLp _

theorem approxL2_norm_le (d a b : Vertex) (n : ℕ) (x y : Vertex) :
    ‖approxL2 d a b n x y‖ ≤ ‖passageL2 x y‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coe_approxL2 d a b n x y, coe_passageL2 x y,
    planarTargetCocycle_dominated d a b ((n+1)*(n+1)) (n+1) (by nlinarith) (by omega)] with ω hc hp hd
  rw [hc, hp, Real.norm_eq_abs, Real.norm_eq_abs]
  exact (hd x y).trans (le_abs_self _)

theorem approxL2_add (d a b : Vertex) (n : ℕ) (x y z : Vertex) :
    approxL2 d a b n x z = approxL2 d a b n x y + approxL2 d a b n y z := by
  apply Lp.ext
  filter_upwards [coe_approxL2 d a b n x z, coe_approxL2 d a b n x y,
    coe_approxL2 d a b n y z, Lp.coeFn_add (approxL2 d a b n x y) (approxL2 d a b n y z)]
    with ω hx hy hz ha
  rw [hx, ha, Pi.add_apply, hy, hz]
  exact planarTargetCocycle_add d a b _ _ ω x y z

noncomputable def translationL2 (a : Vertex) : CalibrationL2 →L[ℝ] CalibrationL2 :=
  (Lp.compMeasurePreservingₗᵢ ℝ (environmentTranslation a)
    (environmentTranslation_preserving a)).toContinuousLinearMap

lemma coe_translationL2 (a : Vertex) (f : CalibrationL2) :
    translationL2 a f =ᵐ[environmentLaw] fun ω => f (environmentTranslation a ω) :=
  Lp.coeFn_compMeasurePreserving f (environmentTranslation_preserving a)

theorem approxL2_shift_norm_le (d a b : Vertex) (n : ℕ) (x y : Vertex) :
    ‖translationL2 a (approxL2 d a b n x y) - approxL2 d a b n (a+x) (a+y)‖ ≤
      (2/(n+1))*‖passageL2 (a+x) (a+y)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  have hcomp := (environmentTranslation_preserving a).quasiMeasurePreserving.ae
    (coe_approxL2 d a b n x y)
  filter_upwards [coe_translationL2 a (approxL2 d a b n x y), hcomp,
    coe_approxL2 d a b n (a+x) (a+y), coe_passageL2 (a+x) (a+y),
    Lp.coeFn_sub (translationL2 a (approxL2 d a b n x y)) (approxL2 d a b n (a+x) (a+y)),
    planarTargetCocycle_shift_bound d a b x y ((n+1)*(n+1)) (n+1) (by nlinarith) (by omega)]
    with ω ht hc he hp hs hb
  rw [hs, Pi.sub_apply, ht, hc, he, hp, Real.norm_eq_abs, Real.norm_eq_abs]
  calc
    _ ≤ 2*passageTime ω (a+x) (a+y)/(n+1) := by exact_mod_cast hb
    _ ≤ (2/(n+1))*|passageTime ω (a+x) (a+y)| := by
      calc
        _ = (2/((n : ℝ)+1))*passageTime ω (a+x) (a+y) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)

theorem approxL2_shift_tendsto (d a b x y : Vertex) :
    Tendsto (fun n : ℕ => translationL2 a (approxL2 d a b n x y) -
      approxL2 d a b n (a+x) (a+y)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => approxL2_shift_norm_le d a b n x y)
  have h := ((tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp
    (tendsto_add_atTop_nat 1)).mul_const ‖passageL2 (a+x) (a+y)‖
  simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, zero_mul] using h

theorem exists_calibration_weak_limit (d a b : Vertex) :
    ∃ (B : Vertex → Vertex → CalibrationL2) (l : Filter ℕ), l.NeBot ∧ l ≤ atTop ∧
      ∀ x y, Tendsto (fun n => toWeakSpace ℝ CalibrationL2 (approxL2 d a b n x y)) l
        (𝓝 (toWeakSpace ℝ CalibrationL2 (B x y))) := by
  obtain ⟨u,l,hl,hle,hu⟩ := exists_weak_product_limit
    (fun n (p : Vertex × Vertex) => approxL2 d a b n p.1 p.2)
    (fun p => ‖passageL2 p.1 p.2‖) (fun n p => approxL2_norm_le d a b n p.1 p.2)
  refine ⟨fun x y => (toWeakSpace ℝ CalibrationL2).symm (u (x,y)), l, hl, hle, ?_⟩
  intro x y
  exact (continuous_apply (x,y)).tendsto (u) |>.comp hu

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_WeakCalibration
attribute [-instance] _root_.OAI.CompanionFPP.encodable_lattice_walk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory Real Filter Topology

lemma convex_calibrationL2_Icc (u v : CalibrationL2) : Convex ℝ (Set.Icc u v) := by
  intro f hf g hg a b ha hb hab
  have hu₁ := (Lp.coeFn_le u f).mpr hf.1
  have hv₁ := (Lp.coeFn_le f v).mpr hf.2
  have hu₂ := (Lp.coeFn_le u g).mpr hg.1
  have hv₂ := (Lp.coeFn_le g v).mpr hg.2
  have he : ∀ᵐ ω ∂environmentLaw, (a • f + b • g) ω = a*f ω+b*g ω := by
    filter_upwards [Lp.coeFn_add (a • f) (b • g), Lp.coeFn_smul a f, Lp.coeFn_smul b g]
      with ω h₁ h₂ h₃
    simp only [h₁, Pi.add_apply, h₂, h₃, Pi.smul_apply, smul_eq_mul]
  constructor
  · apply (Lp.coeFn_le _ _).mp
    filter_upwards [hu₁,hu₂,he] with ω h₁ h₂ he
    rw [he]
    calc
      u ω = a*u ω+b*u ω := by rw [← add_mul, hab, one_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h₁ ha) (mul_le_mul_of_nonneg_left h₂ hb)
  · apply (Lp.coeFn_le _ _).mp
    filter_upwards [hv₁,hv₂,he] with ω h₁ h₂ he
    rw [he]
    calc
      _ ≤ a*v ω+b*v ω := add_le_add (mul_le_mul_of_nonneg_left h₁ ha) (mul_le_mul_of_nonneg_left h₂ hb)
      _ = v ω := by rw [← add_mul, hab, one_mul]

lemma approxL2_mem_Icc (d a b : Vertex) (n : ℕ) (x y : Vertex) :
    approxL2 d a b n x y ∈ Set.Icc (-passageL2 x y) (passageL2 x y) := by
  have he : ∀ᵐ ω ∂environmentLaw,
      -(passageL2 x y) ω ≤ (approxL2 d a b n x y) ω ∧
      (approxL2 d a b n x y) ω ≤ (passageL2 x y) ω := by
    filter_upwards [coe_approxL2 d a b n x y, coe_passageL2 x y,
      planarTargetCocycle_dominated d a b ((n+1)*(n+1)) (n+1) (by nlinarith) (by omega)] with ω hc hp hd
    rw [hc,hp]
    exact abs_le.mp (hd x y)
  constructor
  · apply (Lp.coeFn_le _ _).mp
    filter_upwards [he,Lp.coeFn_neg (passageL2 x y)] with ω h hn
    simpa only [hn, Pi.neg_apply] using h.1
  · exact (Lp.coeFn_le _ _).mp (he.mono (fun _ h => h.2))

lemma weakLimit_mem_Icc {f : ℕ → CalibrationL2} {u v B : CalibrationL2}
    {l : Filter ℕ} [l.NeBot]
    (hconv : Tendsto (fun n => toWeakSpace ℝ CalibrationL2 (f n)) l
      (𝓝 (toWeakSpace ℝ CalibrationL2 B))) (hb : ∀ n, f n ∈ Set.Icc u v) :
    B ∈ Set.Icc u v := by
  have hc := isClosed_weakImage (convex_calibrationL2_Icc u v) isClosed_Icc
  have hmem := hc.mem_of_tendsto hconv (Eventually.of_forall (fun n => ⟨f n,hb n,rfl⟩))
  obtain ⟨g,hg,he⟩ := hmem
  have heq := (toWeakSpace ℝ CalibrationL2).injective he
  exact heq ▸ hg

noncomputable def meanL2 : CalibrationL2 →L[ℝ] ℝ :=
  innerSL ℝ ((memLp_const (μ := environmentLaw) (p := 2) (1 : ℝ)).toLp (fun _ => 1))

lemma meanL2_eq_integral (f : CalibrationL2) : meanL2 f = ∫ ω, f ω ∂environmentLaw := by
  change inner ℝ _ f = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (memLp_const (μ := environmentLaw) (p := 2) (1 : ℝ))] with ω hω
  simp [RCLike.inner_apply]

lemma weak_eval_continuous (F : CalibrationL2 →L[ℝ] ℝ) :
    Continuous (fun f : WeakSpace ℝ CalibrationL2 => F ((toWeakSpace ℝ CalibrationL2).symm f)) :=
  WeakBilin.eval_continuous _ F

lemma approxL2_swap (d a b : Vertex) (n : ℕ) (x y : Vertex) :
    approxL2 d a b n x y = approxL2 d b a n x y := by
  apply Lp.ext
  filter_upwards [coe_approxL2 d a b n x y, coe_approxL2 d b a n x y] with ω h₁ h₂
  rw [h₁,h₂]
  exact planarTargetCocycle_swap d a b _ _ ω x y

theorem calibration_weak_limit_properties (d a b : Vertex)
    (B : Vertex → Vertex → CalibrationL2) (l : Filter ℕ) [l.NeBot] (hle : l ≤ atTop)
    (hconv : ∀ x y, Tendsto (fun n => toWeakSpace ℝ CalibrationL2 (approxL2 d a b n x y)) l
      (𝓝 (toWeakSpace ℝ CalibrationL2 (B x y)))) :
    (∀ x y, B x y ∈ Set.Icc (-passageL2 x y) (passageL2 x y)) ∧
    (∀ x y z, B x z = B x y + B y z) ∧
    meanL2 (B 0 d) = directionalMeanConstant d ∧
    (∀ x y, translationL2 a (B x y) = B (a+x) (a+y)) ∧
    (∀ x y, translationL2 b (B x y) = B (b+x) (b+y)) := by
  refine ⟨fun x y => weakLimit_mem_Icc (hconv x y) (fun n => approxL2_mem_Icc d a b n x y), ?_, ?_, ?_, ?_⟩
  · intro x y z
    apply (toWeakSpace ℝ CalibrationL2).injective
    have h := (hconv x y).add (hconv y z)
    simp only [← map_add, ← approxL2_add] at h
    exact tendsto_nhds_unique (hconv x z) h
  · have hm := ((weak_eval_continuous meanL2).tendsto _).comp (hconv 0 d)
    have he : ∀ n, meanL2 (approxL2 d a b n 0 d) =
        ∫ ω, calibrationApprox d a b n ω 0 d ∂environmentLaw := by
      intro n
      rw [meanL2_eq_integral]
      exact integral_congr_ae (coe_approxL2 d a b n 0 d)
    have hm' : Tendsto (fun n => meanL2 (approxL2 d a b n 0 d)) l
        (𝓝 (directionalMeanConstant d)) := by
      simp_rw [he]
      exact (calibrationApprox_mean_tendsto d a b).mono_left hle
    exact tendsto_nhds_unique hm hm'
  · intro x y
    have h := (((WeakSpace.map (translationL2 a)).continuous.tendsto _).comp (hconv x y)).sub
      (hconv (a+x) (a+y))
    have hz := (toWeakSpaceCLM ℝ CalibrationL2).continuous.tendsto 0 |>.comp
      ((approxL2_shift_tendsto d a b x y).mono_left hle)
    have he : toWeakSpace ℝ CalibrationL2 (translationL2 a (B x y) - B (a+x) (a+y)) =
        toWeakSpace ℝ CalibrationL2 0 := tendsto_nhds_unique h hz
    exact sub_eq_zero.mp ((toWeakSpace ℝ CalibrationL2).injective he)
  · intro x y
    have h := (((WeakSpace.map (translationL2 b)).continuous.tendsto _).comp (hconv x y)).sub
      (hconv (b+x) (b+y))
    have hz' := approxL2_shift_tendsto d b a x y
    simp_rw [approxL2_swap d b a] at hz'
    have hz := (toWeakSpaceCLM ℝ CalibrationL2).continuous.tendsto 0 |>.comp (hz'.mono_left hle)
    have he : toWeakSpace ℝ CalibrationL2 (translationL2 b (B x y) - B (b+x) (b+y)) =
        toWeakSpace ℝ CalibrationL2 0 := tendsto_nhds_unique h hz
    exact sub_eq_zero.mp ((toWeakSpace ℝ CalibrationL2).injective he)

theorem exists_directional_calibrationL2 (d a b : Vertex) :
    ∃ B : Vertex → Vertex → CalibrationL2,
    (∀ x y, B x y ∈ Set.Icc (-passageL2 x y) (passageL2 x y)) ∧
    (∀ x y z, B x z = B x y + B y z) ∧
    meanL2 (B 0 d) = directionalMeanConstant d ∧
    (∀ x y, translationL2 a (B x y) = B (a+x) (a+y)) ∧
    (∀ x y, translationL2 b (B x y) = B (b+x) (b+y)) := by
  obtain ⟨B,l,hl,hle,hconv⟩ := exists_calibration_weak_limit d a b
  let : l.NeBot := hl
  exact ⟨B, calibration_weak_limit_properties d a b B l hle hconv⟩

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_StationaryCalibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory Filter Topology

lemma environmentTranslation_zero (ω : Environment) : environmentTranslation 0 ω = ω := by
  funext e
  unfold environmentTranslation
  congr 1
  apply Subtype.ext
  change Sym2.map (fun x : Vertex => 0+x) e.val = e.val
  simp

lemma translationL2_zero (f : CalibrationL2) : translationL2 0 f = f := by
  apply Lp.ext
  filter_upwards [coe_translationL2 0 f] with ω hω
  simpa only [environmentTranslation_zero] using hω

lemma translationL2_add (a b : Vertex) (f : CalibrationL2) :
    translationL2 (a+b) f = translationL2 a (translationL2 b f) := by
  apply Lp.ext
  have hc := (environmentTranslation_preserving a).quasiMeasurePreserving.ae (coe_translationL2 b f)
  filter_upwards [coe_translationL2 (a+b) f, coe_translationL2 a (translationL2 b f), hc]
    with ω h₁ h₂ h₃
  rw [h₁,h₂,h₃,environmentTranslation_add]

lemma translationL2_injective (a : Vertex) : Function.Injective (translationL2 a) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (E := ℝ) (p := 2) (environmentTranslation a)
    (environmentTranslation_preserving a)).injective

noncomputable def calibrationCovarianceSubgroup (B : Vertex → Vertex → CalibrationL2) :
    AddSubgroup Vertex where
  carrier := {a | ∀ x y, translationL2 a (B x y) = B (a+x) (a+y)}
  zero_mem' := by intro x y; simp only [translationL2_zero, zero_add]
  add_mem' := by
    intro a b ha hb x y
    rw [translationL2_add, hb, ha]
    simp only [add_assoc]
  neg_mem' := by
    intro a ha x y
    apply translationL2_injective a
    rw [← translationL2_add, add_neg_cancel, translationL2_zero, ha]
    simp only [add_neg_cancel_left]

lemma covariance_of_generators (B : Vertex → Vertex → CalibrationL2)
    (h₁ : ∀ x y, translationL2 (1,0) (B x y) = B ((1,0)+x) ((1,0)+y))
    (h₂ : ∀ x y, translationL2 (0,1) (B x y) = B ((0,1)+x) ((0,1)+y)) :
    ∀ a x y, translationL2 a (B x y) = B (a+x) (a+y) := by
  intro a
  have hmem : a ∈ calibrationCovarianceSubgroup B := by
    have he : a = a.1 • ((1,0) : Vertex) + a.2 • ((0,1) : Vertex) := by ext <;> simp
    rw [he]
    exact (calibrationCovarianceSubgroup B).add_mem
      ((calibrationCovarianceSubgroup B).zsmul_mem h₁ a.1)
      ((calibrationCovarianceSubgroup B).zsmul_mem h₂ a.2)
  exact hmem

structure DirectionalCalibration (d : Vertex) where
  value : Environment → Vertex → Vertex → ℝ
  measurable : ∀ x y, Measurable (fun ω => value ω x y)
  memLp : ∀ x y, MemLp (fun ω => value ω x y) 2 environmentLaw
  dominated : ∀ᵐ ω ∂environmentLaw, ∀ x y, |value ω x y| ≤ passageTime ω x y
  additive : ∀ᵐ ω ∂environmentLaw, ∀ x y z, value ω x z = value ω x y+value ω y z
  covariant : ∀ᵐ ω ∂environmentLaw, ∀ a x y,
    value (environmentTranslation a ω) x y = value ω (a+x) (a+y)
  directional_mean : (∫ ω, value ω 0 d ∂environmentLaw) = directionalMeanConstant d

theorem exists_directionalCalibration (d : Vertex) : Nonempty (DirectionalCalibration d) := by
  obtain ⟨B,hdom,hadd,hmean,h₁,h₂⟩ := exists_directional_calibrationL2 d (1,0) (0,1)
  have hcov := covariance_of_generators B h₁ h₂
  refine ⟨{ value := fun ω x y => B x y ω
            measurable := fun x y => (Lp.stronglyMeasurable (B x y)).measurable
            memLp := fun x y => Lp.memLp (B x y)
            dominated := ?_
            additive := ?_
            covariant := ?_
            directional_mean := ?_ }⟩
  · apply ae_all_iff.mpr
    intro x
    apply ae_all_iff.mpr
    intro y
    have hlow := (Lp.coeFn_le _ _).mpr (hdom x y).1
    have hupp := (Lp.coeFn_le _ _).mpr (hdom x y).2
    filter_upwards [hlow,hupp,coe_passageL2 x y,Lp.coeFn_neg (passageL2 x y)]
      with ω hl hu hp hn
    apply abs_le.mpr
    rw [hn,Pi.neg_apply,hp] at hl
    rw [hp] at hu
    exact ⟨hl,hu⟩
  · apply ae_all_iff.mpr
    intro x
    apply ae_all_iff.mpr
    intro y
    apply ae_all_iff.mpr
    intro z
    have h := Lp.coeFn_add (B x y) (B y z)
    rw [← hadd] at h
    exact h
  · apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro x
    apply ae_all_iff.mpr
    intro y
    have h := coe_translationL2 a (B x y)
    rw [hcov] at h
    exact h.symm
  · rwa [meanL2_eq_integral] at hmean

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_CalibrationMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory Filter Topology
namespace DirectionalCalibration
variable {d : Vertex} (C : DirectionalCalibration d)

lemma integrable (x y : Vertex) : Integrable (fun ω => C.value ω x y) environmentLaw :=
  MemLp.integrable (by norm_num) (C.memLp x y)

lemma mean_translation (a x y : Vertex) :
    (∫ ω, C.value ω (a+x) (a+y) ∂environmentLaw) =
      ∫ ω, C.value ω x y ∂environmentLaw := by
  calc
    _ = ∫ ω, C.value (environmentTranslation a ω) x y ∂environmentLaw := by
      apply integral_congr_ae
      filter_upwards [C.covariant] with ω hω
      exact (hω a x y).symm
    _ = _ := by
      have h := integral_map (μ := environmentLaw) (measurable_environmentTranslation a).aemeasurable
        (C.measurable x y).aestronglyMeasurable
      rw [(environmentTranslation_preserving a).map_eq] at h
      exact h.symm

noncomputable def meanHom : Vertex →+ ℝ where
  toFun x := ∫ ω, C.value ω 0 x ∂environmentLaw
  map_zero' := by
    apply integral_eq_zero_of_ae
    filter_upwards [C.additive] with ω hω
    have h := hω 0 0 0
    change C.value ω 0 0 = 0
    linarith
  map_add' x y := by
    have he : (∫ ω, C.value ω 0 (x+y) ∂environmentLaw) =
        (∫ ω, C.value ω 0 x ∂environmentLaw) + (∫ ω, C.value ω x (x+y) ∂environmentLaw) := by
      rw [← integral_add (C.integrable 0 x) (C.integrable x (x+y))]
      apply integral_congr_ae
      filter_upwards [C.additive] with ω hω
      exact hω 0 x (x+y)
    have ht := C.mean_translation x 0 y
    simp only [add_zero] at ht
    exact he.trans (congrArg (_ + ·) ht)

lemma meanHom_direction : C.meanHom d = directionalMeanConstant d := C.directional_mean

lemma scaleVertex_eq_nsmul (n : ℕ) (x : Vertex) : scaleVertex n x = n • x := by
  ext <;> simp [scaleVertex]

lemma meanHom_scale (n : ℕ) (x : Vertex) : C.meanHom (scaleVertex n x) = (n : ℝ)*C.meanHom x := by
  rw [scaleVertex_eq_nsmul, map_nsmul, nsmul_eq_mul]

lemma meanHom_le_mean (x : Vertex) :
    C.meanHom x ≤ ∫ ω, passageTime ω 0 x ∂environmentLaw := by
  apply integral_mono_ae (C.integrable 0 x) (integrable_passageTime 0 x)
  filter_upwards [C.dominated] with ω hω
  exact (le_abs_self _).trans (hω 0 x)

theorem meanHom_le_directionalMeanConstant (x : Vertex) : C.meanHom x ≤ directionalMeanConstant x := by
  apply ge_of_tendsto (meanPassageSequence_tendsto x)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h := C.meanHom_le_mean (scaleVertex n x)
  rw [C.meanHom_scale] at h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  change (n : ℝ)*C.meanHom x ≤ meanPassageSequence x n at h
  exact (le_div_iff₀ hn').mpr (by simpa only [mul_comm (C.meanHom x)] using h)

lemma meanHom_coordinates (x : Vertex) :
    C.meanHom x = (x.1 : ℝ)*C.meanHom (1,0)+(x.2 : ℝ)*C.meanHom (0,1) := by
  have he : x = x.1 • ((1,0) : Vertex) + x.2 • ((0,1) : Vertex) := by ext <;> simp
  conv_lhs => rw [he, map_add, map_zsmul, map_zsmul]
  simp only [zsmul_eq_mul]

noncomputable def meanLinear : Plane →ₗ[ℝ] ℝ where
  toFun x := x.1*C.meanHom (1,0)+x.2*C.meanHom (0,1)
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add]; ring
  map_smul' c x := by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring

lemma meanLinear_embed (x : Vertex) : C.meanLinear (embed x) = C.meanHom x :=
  (C.meanHom_coordinates x).symm

end DirectionalCalibration

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIS_PlanarFPP.LatticePassage_TimeConstantNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory Real Filter Topology Set
open scoped NNReal

lemma meanPassageSequence_neg (x : Vertex) (n : ℕ) :
    meanPassageSequence (-x) n = meanPassageSequence x n := by
  have he : scaleVertex n (-x) = -(scaleVertex n x) := by ext <;> simp [scaleVertex]
  unfold meanPassageSequence
  rw [he]
  have ht := mean_passageTime_translation (-(scaleVertex n x)) (scaleVertex n x) 0
  simp only [neg_add_cancel, add_zero] at ht
  rw [ht]
  apply integral_congr_ae
  filter_upwards [passageTime_properties] with ω hω
  exact hω.2.2.1 _ _

lemma directionalMeanConstant_neg (x : Vertex) : directionalMeanConstant (-x) = directionalMeanConstant x := by
  have h := meanPassageSequence_tendsto (-x)
  simp_rw [meanPassageSequence_neg] at h
  exact tendsto_nhds_unique h (meanPassageSequence_tendsto x)

lemma DirectionalCalibration.abs_meanHom_le {d : Vertex} (C : DirectionalCalibration d) (x : Vertex) :
    |C.meanHom x| ≤ directionalMeanConstant x := by
  apply abs_le.mpr
  have hp := C.meanHom_le_directionalMeanConstant x
  have hn := C.meanHom_le_directionalMeanConstant (-x)
  rw [map_neg, directionalMeanConstant_neg] at hn
  exact ⟨by linarith,hp⟩

lemma DirectionalCalibration.abs_meanHom_le_distance {d : Vertex} (C : DirectionalCalibration d) (x : Vertex) :
    |C.meanHom x| ≤ (latticeDistance 0 x : ℝ) :=
  (C.abs_meanHom_le x).trans ((directionalMeanConstant_le_mean x).trans (mean_passageTime_le_distance 0 x))

noncomputable def chosenCalibration (d : Vertex) : DirectionalCalibration d :=
  Classical.choice (exists_directionalCalibration d)

noncomputable def supportSeminorm (d : Vertex) : Seminorm ℝ Plane :=
  (normSeminorm ℝ ℝ).comp (chosenCalibration d).meanLinear

lemma supportSeminorm_apply (d : Vertex) (v : Plane) :
    supportSeminorm d v = |v.1*(chosenCalibration d).meanHom (1,0)+
      v.2*(chosenCalibration d).meanHom (0,1)| := rfl

lemma supportSeminorm_bound (d : Vertex) (v : Plane) : supportSeminorm d v ≤ 2*‖v‖ := by
  have h₁ : |(chosenCalibration d).meanHom (1,0)| ≤ 1 := by
    simpa [latticeDistance] using (chosenCalibration d).abs_meanHom_le_distance (1,0)
  have h₂ : |(chosenCalibration d).meanHom (0,1)| ≤ 1 := by
    simpa [latticeDistance] using (chosenCalibration d).abs_meanHom_le_distance (0,1)
  rw [supportSeminorm_apply]
  calc
    _ ≤ |v.1| * |(chosenCalibration d).meanHom (1,0)|+
        |v.2| * |(chosenCalibration d).meanHom (0,1)| := by
      simpa only [abs_mul] using abs_add_le (v.1*(chosenCalibration d).meanHom (1,0))
        (v.2*(chosenCalibration d).meanHom (0,1))
    _ ≤ |v.1|+|v.2| := by
      nlinarith [mul_le_mul_of_nonneg_left h₁ (abs_nonneg v.1),
        mul_le_mul_of_nonneg_left h₂ (abs_nonneg v.2)]
    _ ≤ 2*‖v‖ := by
      have hfst := norm_fst_le v
      have hsnd := norm_snd_le v
      simp only [Real.norm_eq_abs] at hfst hsnd
      linarith

lemma supportSeminorm_bddAbove : BddAbove (range supportSeminorm) := by
  refine ⟨(2 : ℝ≥0) • normSeminorm ℝ Plane, ?_⟩
  rintro _ ⟨d,rfl⟩ v
  exact supportSeminorm_bound d v

noncomputable def timeSeminorm : Seminorm ℝ Plane := ⨆ d : Vertex, supportSeminorm d

lemma timeSeminorm_bound (v : Plane) : timeSeminorm v ≤ 2*‖v‖ := by
  rw [timeSeminorm, Seminorm.iSup_apply supportSeminorm_bddAbove]
  exact ciSup_le (fun d => supportSeminorm_bound d v)

lemma timeSeminorm_continuous : Continuous timeSeminorm := by
  apply Seminorm.continuous_of_le (q := (2 : ℝ≥0) • normSeminorm ℝ Plane)
    (show Continuous (fun v : Plane => (2 : ℝ)*‖v‖) by fun_prop)
  exact timeSeminorm_bound

theorem timeSeminorm_embed (x : Vertex) : timeSeminorm (embed x) = directionalMeanConstant x := by
  have he (d : Vertex) : supportSeminorm d (embed x) = |(chosenCalibration d).meanHom x| := by
    change |(chosenCalibration d).meanLinear (embed x)| = _
    rw [(chosenCalibration d).meanLinear_embed]
  rw [timeSeminorm, Seminorm.iSup_apply supportSeminorm_bddAbove]
  apply le_antisymm
  · apply ciSup_le
    intro d
    rw [he]
    exact (chosenCalibration d).abs_meanHom_le x
  · have hb : BddAbove (range (fun d => supportSeminorm d (embed x))) :=
      ⟨2*‖embed x‖,by rintro _ ⟨d,rfl⟩; exact supportSeminorm_bound d (embed x)⟩
    have h := le_ciSup hb x
    rw [he, (chosenCalibration x).meanHom_direction, abs_of_nonneg (directionalMeanConstant_nonneg x)] at h
    exact h

lemma scaled_floor_tendsto (r : ℝ) :
    Tendsto (fun n : ℕ => (⌊(n+1 : ℝ)*r⌋ : ℝ)/(n+1)) atTop (𝓝 r) := by
  have hl : ∀ n : ℕ, r-1/(n+1 : ℝ) ≤ (⌊(n+1 : ℝ)*r⌋ : ℝ)/(n+1) := by
    intro n
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < n+1), sub_mul,
      div_mul_cancel₀ _ (by positivity : (n+1 : ℝ) ≠ 0)]
    linarith [Int.lt_floor_add_one ((n+1 : ℝ)*r)]
  have hu : ∀ n : ℕ, (⌊(n+1 : ℝ)*r⌋ : ℝ)/(n+1) ≤ r := by
    intro n
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < n+1)).mpr
    simpa only [mul_comm r] using Int.floor_le ((n+1 : ℝ)*r)
  have hlim := (tendsto_const_nhds (x := r) (f := atTop)).sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hlim)
    tendsto_const_nhds hl hu

noncomputable def floorVertex (v : Plane) (n : ℕ) : Vertex := (⌊(n+1 : ℝ)*v.1⌋,⌊(n+1 : ℝ)*v.2⌋)

lemma floorVertex_scaled_tendsto (v : Plane) :
    Tendsto (fun n : ℕ => (1/(n+1 : ℝ)) • embed (floorVertex v n)) atTop (𝓝 v) := by
  have h := (scaled_floor_tendsto v.1).prodMk_nhds (scaled_floor_tendsto v.2)
  simpa only [floorVertex, embed, Prod.smul_mk, smul_eq_mul, one_div, div_eq_mul_inv, mul_comm, one_mul, Prod.mk.eta] using h

lemma timeSeminorm_scaled_lattice_lower (x : Vertex) (a : ℝ) (ha : 0 ≤ a) :
    (log 2/20)*(|(a • embed x).1|+|(a • embed x).2|) ≤ timeSeminorm (a • embed x) := by
  have h := mul_le_mul_of_nonneg_left (directionalMeanConstant_linear_lower x) ha
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg ha, timeSeminorm_embed]
  have he : (latticeDistance 0 x : ℝ) = |(x.1 : ℝ)|+|(x.2 : ℝ)| := by
    simp [latticeDistance]
  rw [he] at h
  simpa only [embed, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul, abs_of_nonneg ha,
    mul_add, mul_assoc, mul_left_comm] using h

theorem timeSeminorm_linear_lower (v : Plane) :
    (log 2/20)*(|v.1|+|v.2|) ≤ timeSeminorm v := by
  have h := floorVertex_scaled_tendsto v
  have hl := ((continuous_fst.tendsto v).comp h).abs.add (((continuous_snd.tendsto v).comp h).abs)
  apply le_of_tendsto_of_tendsto (hl.const_mul (log 2/20)) (timeSeminorm_continuous.tendsto v |>.comp h)
  exact Eventually.of_forall (fun n => timeSeminorm_scaled_lattice_lower (floorVertex v n) _ (by positivity))

noncomputable def actualTimeNorm : TimeNorm where
  seminorm := timeSeminorm
  definite v hv := by
    have h := timeSeminorm_linear_lower v
    rw [hv] at h
    have hc : 0 < log 2/20 := by positivity
    have hz : |v.1|+|v.2| = 0 := by nlinarith [abs_nonneg v.1,abs_nonneg v.2]
    have h₁ : v.1 = 0 := abs_eq_zero.mp (by linarith [abs_nonneg v.1,abs_nonneg v.2])
    have h₂ : v.2 = 0 := abs_eq_zero.mp (by linarith [abs_nonneg v.1,abs_nonneg v.2])
    exact Prod.ext h₁ h₂

end CompanionFPP

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

def BoundedIndexSteps : (ℤ×ℤ) → List (ℤ×ℤ) → Prop
  | _,[] => True
  | p,q::qs => |q.1-p.1| ≤ 3 ∧ |q.2-p.2| ≤ 3 ∧ BoundedIndexSteps q qs

end PlanarFPP

end OAI
end


