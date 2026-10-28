-- Prove2me | Definitions.Def_OAIQ034H005
-- name    : OAIQ034H005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T05:36:25.981968+00:00
-- url     : https://prove2.me/theorems/b1af1d20-3dbd-4d44-a706-f661bd0e74c7
-- title:
--   Definitions bundle OAIQ034H005 of the split of OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HyperbolicObstruction.main`, carved from OpenAI's openai/math development (OpenAI, *A hyperbolic group with no geometric CAT(0) action (result family 257)*, OpenAI Math Release, September 25, 2026, result family 257, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 388 declarations of OpenAI's Lean: 104 definitions, 9 inductive types or structures, 7 instances and 268 theorems. The definitions and types are `OAI.HyperbolicObstruction.ConeSkeleton.apexInstanceAt`, `OAI.HyperbolicObstruction.ConeSkeleton.cellWalkStep`, `OAI.HyperbolicObstruction.ConeSkeleton.fanPotential`, `OAI.HyperbolicObstruction.ConeSkeleton.frozenOffset`, `OAI.HyperbolicObstruction.ConeSkeleton.indexingFrozenTarget`, `OAI.HyperbolicObstruction.ConeSkeleton.indexingTarget`, `OAI.HyperbolicObstruction.ConeSkeleton.partSelect`, `OAI.HyperbolicObstruction.ConeSkeleton.radialValue`, `OAI.HyperbolicObstruction.ConeSkeleton.topDart`, `OAI.HyperbolicObstruction.CoreGeometry.ExceptionalTest`, `OAI.HyperbolicObstruction.CoreGeometry.HexagonCode.vertices`, `OAI.HyperbolicObstruction.CoreGeometry.MetricCore.center`, `OAI.HyperbolicObstruction.CoreWordGraph.projection`, `OAI.HyperbolicObstruction.EdgeContraction.contraction`, `OAI.HyperbolicObstruction.EdgeContraction.square`, `OAI.HyperbolicObstruction.EnergyOrbit`, `OAI.HyperbolicObstruction.EnergyOrbit.Cone`, `OAI.HyperbolicObstruction.EnergyOrbit.cone`, `OAI.HyperbolicObstruction.EnergyOrbit.vector`, `OAI.HyperbolicObstruction.FiniteComplex.pathValue`, `OAI.HyperbolicObstruction.FiniteLaw.map`, `OAI.HyperbolicObstruction.FiniteLaw.normalize`, `OAI.HyperbolicObstruction.FiniteLaw.prod`, `OAI.HyperbolicObstruction.FiniteLaw.totalVariation`, `OAI.HyperbolicObstruction.FiniteLaw.uniform`, `OAI.HyperbolicObstruction.FiniteObstructionData`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.collarB`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.collarC`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.cornerOffset`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.cornerPrimitive`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.correctionApex`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.correctionDiagonal`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.correctionIncrement`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.correctionOuter`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.graphCochain`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.graphValue`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.instCommGroupLoopClassVertexVoltage`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.liftedCochain`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.obstructionCochain`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.obstructionWeight` and 73 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/HyperbolicGroups, in whole or in part: `HyperbolicGroups_ActualContact`, `HyperbolicGroups_ActualPartition`, `HyperbolicGroups_CATZeroFurther`, `HyperbolicGroups_Chernoff`, `HyperbolicGroups_ColoredApex`, `HyperbolicGroups_ConditionalStar`, `HyperbolicGroups_Conditioning`, `HyperbolicGroups_ConeCellWalk`, `HyperbolicGroups_ConeCover`, `HyperbolicGroups_ConeData`, `HyperbolicGroups_ConeDecorationGroup`, `HyperbolicGroups_ConeFanGroup`, `HyperbolicGroups_ConeTopGroup`, `HyperbolicGroups_CoreWordGraph`, `HyperbolicGroups_DipoleChain`, `HyperbolicGroups_DipoleRemove`, `HyperbolicGroups_DipoleSwitch`, `HyperbolicGroups_Distinct`, `HyperbolicGroups_EdgeContraction`, `HyperbolicGroups_EdgeMerge`, `HyperbolicGroups_EdgeMergeComponents`, `HyperbolicGroups_FaceWalk`, `HyperbolicGroups_FiberLaw`, `HyperbolicGroups_FiniteLaw`, `HyperbolicGroups_FinitePolygonModel`, `HyperbolicGroups_FinitePolygonVoltage`, `HyperbolicGroups_FinitePolyhedron`, `HyperbolicGroups_FinitePolyhedronDeck`, `HyperbolicGroups_FinitePolyhedronMonodromy`, `HyperbolicGroups_FinitePolyhedronPathAlgebra`, `HyperbolicGroups_FinitePolyhedronVoltage`, `HyperbolicGroups_FiniteSelection`, `HyperbolicGroups_Fragment`, `HyperbolicGroups_FrozenWalk`, `HyperbolicGroups_GeometricAction`, `HyperbolicGroups_Graph`, `HyperbolicGroups_HSpaceFundamental`, `HyperbolicGroups_IndexedFillingValue`, `HyperbolicGroups_IntegralCellularBoundary`, `HyperbolicGroups_LiftedClosedPicture`, `HyperbolicGroups_MappedPicture`, `HyperbolicGroups_MetricHexagon`, `HyperbolicGroups_Moment`, `HyperbolicGroups_Normalization`, `HyperbolicGroups_PictureGenus`, `HyperbolicGroups_PictureMirror`, `HyperbolicGroups_PicturePartition`, `HyperbolicGroups_PictureSum`, `HyperbolicGroups_PolygonContraction`, `HyperbolicGroups_PolygonCornerPrimitive`, `HyperbolicGroups_PolygonLiftedCochain`, `HyperbolicGroups_PolygonSphereFurther`, `HyperbolicGroups_PolygonTarget`, `HyperbolicGroups_PolygonTriangleCochains`, `HyperbolicGroups_PolygonTriangles`, `HyperbolicGroups_ProtectedNormal`, `HyperbolicGroups_RankSelection`, `HyperbolicGroups_SeparatorGrouping`, `HyperbolicGroups_SimplexCoordinates`, `HyperbolicGroups_SquareBoundaryExtension`, `HyperbolicGroups_StarError`, `HyperbolicGroups_StepChain`, `HyperbolicGroups_TangentCone`, `HyperbolicGroups_TangentRay`, `HyperbolicGroups_Template`, `HyperbolicGroups_TreeCentroid`, `HyperbolicGroups_TreeCentroidComponents`, `HyperbolicGroups_TreeCentroidCut`, `HyperbolicGroups_TriangleHomotopyExtension`, `HyperbolicGroups_VoltageClosedCells`, `HyperbolicGroups_VoltageEdgeCorrection`, `HyperbolicGroups_VoltageEdges`, `HyperbolicGroups_VoltageGraphHomotopy`, `HyperbolicGroups_VoltagePrismGluing`, `HyperbolicGroups_VoltageTriangleContraction`, `HyperbolicGroups_VoltageTriangleHomotopy`, `HyperbolicGroups_VoltageTriangles`, `HyperbolicGroups_WalkCancel`, `HyperbolicGroups_WalkCell`, `HyperbolicGroups_WalkCover`, `HyperbolicGroups_WalkFanCapacity`, `HyperbolicGroups_WalkInstanceAt`, `HyperbolicGroups_WalkRadialBoundary`, `HyperbolicGroups_WordPicture`, `HyperbolicGroups_WordPictureAppend`, `HyperbolicGroups_WordPictureCell`.
--
--   **Imports.** It imports the published bundle `Def_HyperbolicObstruction`; the bundles `OAIQ034H000`, `OAIQ034H001` and `OAIQ034H002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ034H008`, `OAIQ034H009` and `OAIQ034H010`.
-- source:
--   OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 257; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-hyperbolic-group-with-no-geometric-CAT0-action-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/HyperbolicGroups at commit adc7f12

import Mathlib
import Definitions.Def_HyperbolicObstruction
import Definitions.Def_OAIQ034H000
import Definitions.Def_OAIQ034H001
import Definitions.Def_OAIQ034H002

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TangentRay
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
namespace HyperbolicObstruction
open Filter Topology UniformSpace
open scoped NNReal
variable {X : Type*} [MetricSpace X]

namespace TangentRay
variable (h : CATZero X) (o : X)

def vertex : TangentRay h o := ⟨0, o⟩
def log (x : X) : TangentRay h o := ⟨1, x⟩

theorem dist_sq (p q : TangentRay h o) :
    dist p q ^ 2 = (p.weight : ℝ) ^ 2 * dist o p.point ^ 2 +
      (q.weight : ℝ) ^ 2 * dist o q.point ^ 2 -
        2 * (p.weight : ℝ) * (q.weight : ℝ) * CATZero.tangentPairing h o p.point q.point :=
  CATZero.tangentDist_sq h o p.point q.point p.weight.coe_nonneg q.weight.coe_nonneg

theorem dist_vertex (p : TangentRay h o) :
    dist (vertex h o) p = (p.weight : ℝ) * dist o p.point :=
  CATZero.tangentDist_zero_left h o o p.point p.weight.coe_nonneg

theorem radial_metric (r s : ℝ≥0) (p q : TangentRay h o) :
    dist (scale h o r p) (scale h o s q) ^ 2 =
      ((r : ℝ) ^ 2 - (r : ℝ) * (s : ℝ)) * dist (vertex h o) p ^ 2 +
      ((s : ℝ) ^ 2 - (r : ℝ) * (s : ℝ)) * dist (vertex h o) q ^ 2 +
      (r : ℝ) * (s : ℝ) * dist p q ^ 2 := by
  rw [dist_sq, dist_vertex, dist_vertex, dist_sq]
  dsimp only [scale, NNReal.coe_mul]
  ring

theorem dist_scale (r : ℝ≥0) (p q : TangentRay h o) :
    dist (scale h o r p) (scale h o r q) = (r : ℝ) * dist p q := by
  have he := radial_metric h o r r p q
  have hn := dist_nonneg (x := scale h o r p) (y := scale h o r q)
  have hn' := mul_nonneg r.coe_nonneg (dist_nonneg (x := p) (y := q))
  nlinarith

theorem scale_lipschitz (r : ℝ≥0) : LipschitzWith r (scale h o r) :=
  LipschitzWith.of_dist_le_mul fun p q => (dist_scale h o r p q).le

end TangentRay


end HyperbolicObstruction
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
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TangentCone
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
namespace HyperbolicObstruction
open Filter Topology UniformSpace
open scoped NNReal
variable {X : Type*} [MetricSpace X]

namespace TangentCone
variable (h : CATZero X) (o : X)

def vertex : TangentCone h o := (TangentRay.vertex h o : TangentRay h o)
def log (x : X) : TangentCone h o := (TangentRay.log h o x : TangentRay h o)

theorem scaleN_coe (r : ℝ≥0) (p : TangentRay h o) :
    scaleN h o r p = (TangentRay.scale h o r p : TangentRay h o) :=
  Completion.map_coe (TangentRay.scale_lipschitz h o r).uniformContinuous p

theorem scaleN_zero (x : TangentCone h o) : scaleN h o 0 x = vertex h o := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (continuous_scaleN h o 0) continuous_const
  | ih p =>
    rw [scaleN_coe]
    apply dist_eq_zero.mp
    rw [vertex, Completion.dist_eq, dist_comm, TangentRay.dist_vertex]
    simp [TangentRay.scale]

theorem scaleN_one (x : TangentCone h o) : scaleN h o 1 x = x := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (continuous_scaleN h o 1) continuous_id
  | ih p =>
    rw [scaleN_coe]
    congr 1
    cases p
    simp [TangentRay.scale]

theorem radial_metric (r s : ℝ≥0) (x y : TangentCone h o) :
    dist (scaleN h o r x) (scaleN h o s y) ^ 2 =
      ((r : ℝ) ^ 2 - (r : ℝ) * (s : ℝ)) * dist (vertex h o) x ^ 2 +
      ((s : ℝ) ^ 2 - (r : ℝ) * (s : ℝ)) * dist (vertex h o) y ^ 2 +
      (r : ℝ) * (s : ℝ) * dist x y ^ 2 := by
  induction x, y using Completion.induction_on₂ with
  | hp =>
    apply isClosed_eq <;> fun_prop
  | ih p q =>
    rw [scaleN_coe, scaleN_coe]
    simpa only [vertex, Completion.dist_eq] using TangentRay.radial_metric h o r s p q

/-- The required radial metric law, with no asserted CAT(0) axiom.
The CAT(0) property is a separate construction below. -/
def coneData : ConeData (TangentCone h o) where
  vertex := vertex h o
  scale r := scaleN h o r.toNNReal
  scale_zero := by simpa only [Real.toNNReal_zero] using scaleN_zero h o
  scale_one := by simpa only [Real.toNNReal_one] using scaleN_one h o
  radial_metric r s hr hs := by
    simpa only [Real.toNNReal_of_nonneg hr, Real.toNNReal_of_nonneg hs, NNReal.coe_mk]
      using radial_metric h o r.toNNReal s.toNNReal

theorem dist_log_le (x y : X) : dist (log h o x) (log h o y) ≤ dist x y := by
  rw [log, log, Completion.dist_eq]
  change CATZero.tangentDist h o x y 1 1 ≤ dist x y
  simpa only [one_mul] using CATZero.tangentDist_le h o x y (r := 1) (by norm_num)

theorem dist_vertex_log (x : X) : dist (vertex h o) (log h o x) = dist o x := by
  rw [vertex, log, Completion.dist_eq, TangentRay.dist_vertex]
  simp only [TangentRay.log, NNReal.coe_one, one_mul]

theorem normSq_log (x : X) : (coneData h o).normSq (log h o x) = dist o x ^ 2 := by
  change dist (vertex h o) (log h o x) ^ 2 = _
  rw [dist_vertex_log]

end TangentCone
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
open Filter Topology UniformSpace
open scoped NNReal

namespace TangentCone
variable {X : Type*} [MetricSpace X] (h : CATZero X) (o : X)

theorem representedMid_left (p q : TangentRay h o) :
    dist (p : TangentCone h o) (representedMid h o p q) = dist p q / 2 :=
  (exists_represented_mid h o p q).choose_spec.1

theorem representedMid_right (p q : TangentRay h o) :
    dist (q : TangentCone h o) (representedMid h o p q) = dist p q / 2 :=
  (exists_represented_mid h o p q).choose_spec.2.1

theorem representedMid_cn (p q : TangentRay h o) (z : TangentCone h o) :
    dist z (representedMid h o p q) ^ 2 ≤ (dist z p ^ 2 + dist z q ^ 2) / 2 -
      dist p q ^ 2 / 4 := (exists_represented_mid h o p q).choose_spec.2.2 z

theorem representedMid_swap (p q : TangentRay h o) :
    representedMid h o p q = representedMid h o q p := by
  have hc := representedMid_cn h o q p (representedMid h o p q)
  rw [dist_comm (representedMid h o p q) q, representedMid_right,
    dist_comm (representedMid h o p q) p, representedMid_left, dist_comm q p] at hc
  apply dist_eq_zero.mp
  nlinarith [dist_nonneg (x := representedMid h o p q) (y := representedMid h o q p)]

theorem representedMid_contraction (p q r : TangentRay h o) :
    dist (representedMid h o p q) (representedMid h o p r) ≤ dist q r / 2 := by
  have hc := representedMid_cn h o p r (representedMid h o p q)
  have hc' := representedMid_cn h o p q (r : TangentCone h o)
  rw [dist_comm (representedMid h o p q) p, representedMid_left,
    dist_comm (representedMid h o p q) r] at hc
  simp only [Completion.dist_eq] at hc'
  rw [dist_comm r p, dist_comm r q] at hc'
  have hn := dist_nonneg (x := q) (y := r)
  nlinarith [dist_nonneg (x := representedMid h o p q) (y := representedMid h o p r)]

theorem representedMid_lipschitz :
    LipschitzWith 1 (fun p : TangentRay h o × TangentRay h o => representedMid h o p.1 p.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have h1 := representedMid_contraction h o p.2 p.1 q.1
  rw [representedMid_swap h o p.2 p.1, representedMid_swap h o p.2 q.1] at h1
  have h2 := representedMid_contraction h o q.1 p.2 q.2
  have ht := dist_triangle (representedMid h o p.1 p.2) (representedMid h o q.1 p.2)
    (representedMid h o q.1 q.2)
  rw [NNReal.coe_one, one_mul, Prod.dist_eq]
  have ha := le_max_left (dist p.1 q.1) (dist p.2 q.2)
  have hb := le_max_right (dist p.1 q.1) (dist p.2 q.2)
  linarith

theorem coneMid_coe (p q : TangentRay h o) : coneMid h o p q = representedMid h o p q :=
  Completion.extension₂_coe_coe (f := representedMid h o)
    (representedMid_lipschitz h o).uniformContinuous p q

theorem coneMid_left (x y : TangentCone h o) :
    dist x (coneMid h o x y) = dist x y / 2 := by
  induction x, y using Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih p q => rw [coneMid_coe, representedMid_left, Completion.dist_eq]

theorem coneMid_cn (x y z : TangentCone h o) :
    dist z (coneMid h o x y) ^ 2 ≤ (dist z x ^ 2 + dist z y ^ 2) / 2 - dist x y ^ 2 / 4 := by
  induction x, y using Completion.induction_on₂ with
  | hp => apply isClosed_le <;> fun_prop
  | ih p q =>
    rw [coneMid_coe, Completion.dist_eq]
    exact representedMid_cn h o p q z

end TangentCone
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
open Filter Topology

/-- Full CAT(0) comparison from complete CN midpoints. The division point
is constructed by minimizing a weighted squared-distance functional. -/
theorem catZero_of_midpoints {Y : Type*} [MetricSpace Y] [CompleteSpace Y]
    (M : Y → Y → Y)
    (hM : ∀ x y, dist x (M x y) = dist x y / 2)
    (hCN : ∀ x y z, dist z (M x y) ^ 2 ≤
      (dist z x ^ 2 + dist z y ^ 2) / 2 - dist x y ^ 2 / 4) : CATZero Y := by
  intro x y
  let : Nonempty Y := ⟨x⟩
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ∃ p : Y, dist x p = t * dist x y ∧ dist p y = (1 - t) * dist x y ∧
        ∀ z, dist z p ^ 2 ≤ (1 - t) * dist z x ^ 2 + t * dist z y ^ 2 -
          t * (1 - t) * dist x y ^ 2 := by
    let f : Y → ℝ := fun z => (1 - t) * dist z x ^ 2 + t * dist z y ^ 2
    have hf : Continuous f := by dsimp only [f]; fun_prop
    have hb : BddBelow (Set.range f) := ⟨0, by
      rintro _ ⟨z, rfl⟩
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (sq_nonneg _))
        (mul_nonneg ht.1 (sq_nonneg _))⟩
    have hc (a b : Y) : f (M a b) ≤ (f a + f b) / 2 - dist a b ^ 2 / 4 := by
      have h1 := mul_le_mul_of_nonneg_left (hCN a b x) (sub_nonneg.mpr ht.2)
      have h2 := mul_le_mul_of_nonneg_left (hCN a b y) ht.1
      simp only [dist_comm x, dist_comm y] at h1 h2
      dsimp only [f]
      nlinarith
    obtain ⟨p, hp⟩ := strongly_convex_minimum M f hf hb hc
    have hv := strongly_convex_variance M hM f hc p hp
    have hx := hv x
    have hy := hv y
    have hx' := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ht.2)
    have hy' := mul_le_mul_of_nonneg_left hy ht.1
    simp only [f, dist_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
      zero_add, add_zero, dist_comm y x] at hx hy hx' hy'
    have hupper : f p ≤ t * (1 - t) * dist x y ^ 2 := by
      dsimp only [f]
      nlinarith
    have htri := dist_triangle x p y
    rw [dist_comm x p] at htri
    have hs : dist x y ^ 2 ≤ (dist p x + dist p y) ^ 2 :=
      (sq_le_sq₀ dist_nonneg (add_nonneg dist_nonneg dist_nonneg)).mpr htri
    have hs' := mul_le_mul_of_nonneg_left hs (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
    have hlower : t * (1 - t) * dist x y ^ 2 ≤ f p := by
      dsimp only [f]
      nlinarith [sq_nonneg ((1 - t) * dist p x - t * dist p y)]
    have hfx : f p = t * (1 - t) * dist x y ^ 2 := le_antisymm hupper hlower
    have hpx : dist p x ≤ t * dist x y := by
      have hl := hlower
      dsimp only [f] at hl
      nlinarith [dist_nonneg (x := p) (y := x),
        mul_nonneg ht.1 (dist_nonneg (x := x) (y := y))]
    have hpy : dist p y ≤ (1 - t) * dist x y := by
      have hl := hlower
      dsimp only [f] at hl
      nlinarith [dist_nonneg (x := p) (y := y),
        mul_nonneg (sub_nonneg.mpr ht.2) (dist_nonneg (x := x) (y := y))]
    refine ⟨p, ?_, by linarith, ?_⟩
    · rw [dist_comm]
      linarith
    · intro z
      have hz := hv z
      rw [hfx, dist_comm p z] at hz
      exact (le_sub_iff_add_le.mpr (by simpa only [f, add_comm] using hz))
  choose point hleft hright hcomp using hpoint
  let γ : ℝ → Y := fun t => if ht : t ∈ Set.Icc (0 : ℝ) 1 then point t ht else x
  have hγ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : γ t = point t ht := dite_eq_left ht
  have hL (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : dist x (γ t) = t * dist x y := by
    rw [hγ t ht]; exact hleft t ht
  have hR (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : dist (γ t) y = (1 - t) * dist x y := by
    rw [hγ t ht]; exact hright t ht
  have hC (z : Y) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      dist z (γ t) ^ 2 ≤ (1 - t) * dist z x ^ 2 + t * dist z y ^ 2 -
        t * (1 - t) * dist x y ^ 2 := by rw [hγ t ht]; exact hcomp t ht z
  refine ⟨γ, ⟨?_, ?_, ?_⟩, hC⟩
  · apply (dist_eq_zero.mp ?_).symm
    simpa only [zero_mul] using hL 0 (by norm_num)
  · apply dist_eq_zero.mp
    simpa only [sub_self, zero_mul] using hR 1 (by norm_num)
  · intro s hs t ht
    have hCN' := hC (γ s) t ht
    rw [dist_comm (γ s) x, hL s hs, hR s hs] at hCN'
    have ha : dist (γ s) (γ t) ≤ |s - t| * dist x y := by
      nlinarith [sq_abs (s - t), mul_nonneg (abs_nonneg (s - t)) (dist_nonneg (x := x) (y := y)),
        dist_nonneg (x := γ s) (y := γ t)]
    have hb1 := dist_triangle x (γ t) (γ s)
    have hb2 := dist_triangle x (γ s) (γ t)
    rw [hL s hs, hL t ht, dist_comm (γ t) (γ s)] at hb1
    rw [hL s hs, hL t ht] at hb2
    rcases le_total t s with hts | hst
    · rw [abs_of_nonneg (sub_nonneg.mpr hts)] at ha ⊢
      linarith
    · rw [abs_of_nonpos (sub_nonpos.mpr hst)] at ha ⊢
      linarith


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

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeData
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
namespace HyperbolicObstruction
open Filter Topology

namespace TangentCone
variable {X : Type*} [MetricSpace X] (h : CATZero X) (o : X)

/-- The constructed completed tangent cone is CAT(0). -/
theorem catZero : CATZero (TangentCone h o) :=
  catZero_of_midpoints (coneMid h o) (coneMid_left h o) (coneMid_cn h o)

end TangentCone
end HyperbolicObstruction

noncomputable section

noncomputable section
namespace HyperbolicObstruction
open Filter Topology UniformSpace
namespace TangentCone
variable {X : Type*} [MetricSpace X] (h : CATZero X)

/-- The log based at any point of a segment is distance preserving on that
segment, including pairs lying on opposite sides of the basepoint. -/
theorem log_dist_on_segment (x y : X) {v s u : ℝ}
    (hv : v ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    dist (log h (CATZero.segment h x y v) (CATZero.segment h x y s))
      (log h (CATZero.segment h x y v) (CATZero.segment h x y u)) =
        dist (CATZero.segment h x y s) (CATZero.segment h x y u) := by
  rw [log, log, Completion.dist_eq, TangentRay.dist_def]
  change CATZero.tangentDist h (CATZero.segment h x y v)
    (CATZero.segment h x y s) (CATZero.segment h x y u) 1 1 = _
  apply tendsto_nhds_unique (CATZero.tangentDist_tendsto h (CATZero.segment h x y v)
    (CATZero.segment h x y s) (CATZero.segment h x y u) (by norm_num) (by norm_num))
  apply tendsto_const_nhds.congr'
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  filter_upwards [show ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t from eventually_mem_nhdsWithin,
    ht.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t ht0 ht1
  rw [mul_one, CATZero.segment_between h x y hv hs ⟨ht0.le, ht1⟩,
    CATZero.segment_between h x y hv hu ⟨ht0.le, ht1⟩]
  have hv' (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
      (1 - t) * v + t * a ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) hv.1) (mul_nonneg ht0.le ha.1)
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hv.2),
        mul_nonneg ht0.le (sub_nonneg.mpr ha.2)]
  rw [(CATZero.segment_spec h x y).2.2 _ (hv' s hs) _ (hv' u hu),
    (CATZero.segment_spec h x y).2.2 s hs u hu,
    show (1 - t) * v + t * s - ((1 - t) * v + t * u) = t * (s - u) by ring,
    abs_mul, abs_of_pos ht0]
  field_simp

theorem log_dist_mid_endpoints (x y : X) :
    dist (log h (CATZero.mid h x y) x) (log h (CATZero.mid h x y) y) = dist x y := by
  have he := log_dist_on_segment h x y
    (v := 1 / 2) (s := 0) (u := 1) (by norm_num) (by norm_num) (by norm_num)
  change dist (log h (CATZero.mid h x y) (CATZero.segment h x y 0))
    (log h (CATZero.mid h x y) (CATZero.segment h x y 1)) =
      dist (CATZero.segment h x y 0) (CATZero.segment h x y 1) at he
  rw [(CATZero.segment_spec h x y).1, (CATZero.segment_spec h x y).2.1] at he
  exact he

theorem opposite_mid_logs (x y : X) :
    (coneData h (CATZero.mid h x y)).Opposite
      (log h (CATZero.mid h x y) x) (log h (CATZero.mid h x y) y) := by
  constructor
  · rw [normSq_log, normSq_log, CATZero.dist_mid_right,
      dist_comm (CATZero.mid h x y) x, CATZero.dist_left_mid]
  · unfold ConeData.pairing
    rw [normSq_log, normSq_log, log_dist_mid_endpoints, CATZero.dist_mid_right,
      dist_comm (CATZero.mid h x y) x, CATZero.dist_left_mid]
    ring

theorem pairing_log_ge (o x y : X) :
    (dist o x ^ 2 + dist o y ^ 2 - dist x y ^ 2) / 2 ≤
      (coneData h o).pairing (log h o x) (log h o y) := by
  have hd := (sq_le_sq₀ dist_nonneg dist_nonneg).mpr (dist_log_le h o x y)
  unfold ConeData.pairing
  rw [normSq_log, normSq_log]
  linarith

end TangentCone
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

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_CATZeroFurther
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

namespace HyperbolicObstruction
namespace TangentCone
variable {X : Type*} [MetricSpace X] (h : CATZero X)

/-- A log-isometric base gives every radial CN equality, directly from the
constructed cone metric law and uniqueness of segments. -/
theorem cn_eq_of_log_dist (o x y : X)
    (he : dist (log h o x) (log h o y) = dist x y) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist o (CATZero.segment h x y t) ^ 2 =
      (1 - t) * dist o x ^ 2 + t * dist o y ^ 2 - t * (1 - t) * dist x y ^ 2 := by
  have hmap := CATZero.map_segment_of_dist h (catZero h o) (log h o)
    (dist_log_le h o) x y he ht
  have hn := (coneData h o).normSq_segment (catZero h o) (log h o x) (log h o y) ht
  rw [← hmap, normSq_log, normSq_log, normSq_log, he] at hn
  exact hn

end TangentCone
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction

/-- The specific subconfiguration used by the source obstruction. This is
metric input to a contradiction, not an assumed existence assertion. All its
conditions are consequences asserted by source Proposition `configuration`;
the existence-from-actions direction remains a separate obligation. -/
structure FiniteObstructionData {X : Type*} [MetricSpace X] (h : CATZero X) where
  c : X
  x : Fin 4 → X
  y : Fin 4 → X
  line : Fin 6 → X
  radiusX : ∀ i, dist c (x i) ^ 2 = 3 / 4
  radiusY : ∀ i, dist c (y i) ^ 2 = 3 / 4
  radiusLine : ∀ i, dist c (line i) ^ 2 = 3 / 4
  lineDist : ∀ a b, a ≠ b → dist (line a) (line b) ^ 2 = 2
  lineFlat : ∀ a b, a ≠ b → dist c (CATZero.mid h (line a) (line b)) ^ 2 = 1 / 4
  square : ∀ i a b, a ∈ fullLines i → b ∈ fullLines i → a ≠ b →
    MetricSquare (x i) (line a) (y i) (line b)
  twoStepX : dist (x 2) (x 3) ^ 2 = 2
  twoStepY : dist (y 2) (x 3) ^ 2 = 2
  loose : dist (line 5) (x 3) ^ 2 = 1
  missing : 3 ≤ dist (y 3) (line 5) ^ 2
  fractional : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
    t ^ 2 * (1 / 2 + 1) ≤
      dist (CATZero.segment h (line 5) (CATZero.mid h (x 2) (y 2)) t)
        (CATZero.segment h (line 5) (x 3) t) ^ 2

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

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_GeometricAction
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
namespace HyperbolicObstruction
open scoped BigOperators

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

def uniform [Nonempty α] : FiniteLaw α where
  mass _ := 1 / (Fintype.card α : ℝ)
  nonneg _ := by positivity
  sum_one := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hh : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp [hh]

theorem expect_sum (μ : FiniteLaw α) {ι : Type*} [Fintype ι] (f : ι → α → ℝ) :
    μ.expect (fun a => ∑ i, f i a) = ∑ i, μ.expect (f i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem expect_nonneg (μ : FiniteLaw α) {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    0 ≤ μ.expect f := Finset.sum_nonneg fun a _ => mul_nonneg (μ.nonneg a) (hf a)

def map (μ : FiniteLaw α) (f : α → β) : FiniteLaw β := by
  classical
  exact {
    mass := fun b => ∑ a, if f a = b then μ.mass a else 0
    nonneg := fun b => Finset.sum_nonneg fun a _ => by
      split
      · exact μ.nonneg a
      · exact le_rfl
    sum_one := by rw [Finset.sum_comm]; simpa using μ.sum_one }

def totalVariation (μ ν : FiniteLaw α) : ℝ := (∑ a, |μ.mass a - ν.mass a|) / 2

theorem totalVariation_nonneg (μ ν : FiniteLaw α) : 0 ≤ μ.totalVariation ν := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)

/-- Finite-probability Cauchy--Schwarz in the scalar form needed for cone
norms under arbitrary conditional couplings. -/
theorem expect_le_sqrt (μ : FiniteLaw α) (f : α → ℝ) :
    μ.expect f ≤ Real.sqrt (μ.expect (fun a => f a ^ 2)) := by
  have hn := μ.expect_nonneg (fun a => sq_nonneg (f a - μ.expect f))
  have he : μ.expect (fun a => (f a - μ.expect f) ^ 2) =
      μ.expect (fun a => f a ^ 2) - μ.expect f ^ 2 := by
    simp_rw [sub_sq, show ∀ a, 2 * f a * μ.expect f = (2 * μ.expect f) * f a by intro a; ring]
    rw [μ.expect_add, μ.expect_sub, μ.expect_mul, μ.expect_const]
    ring
  rw [he] at hn
  have hpos := μ.expect_nonneg (fun a => sq_nonneg (f a))
  have hs := Real.sq_sqrt hpos
  have hs' := Real.sqrt_nonneg (μ.expect (fun a => f a ^ 2))
  nlinarith

end FiniteLaw
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

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FiniteLaw
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
namespace HyperbolicObstruction

namespace MetricHexagon
variable {X : Type*} [MetricSpace X] {z : Fin 6 → X}

theorem rigidity (D : MetricHexagon z) (h : CATZero X) :
    (∀ i j, dist (z i) (z j) ^ 2 = hexDistSq i j) ∧
    (∀ j, CATZero.mid h (z j) (z (j + 3)) = CATZero.mid h (z 0) (z 3)) := by
  have hs0 : dist (z 0) (z 1) ^ 2 = 1 := D.side 0
  have hs1 : dist (z 1) (z 2) ^ 2 = 1 := D.side 1
  have hs2 : dist (z 2) (z 3) ^ 2 = 1 := D.side 2
  have hs3 : dist (z 3) (z 4) ^ 2 = 1 := D.side 3
  have hs4 : dist (z 4) (z 5) ^ 2 = 1 := D.side 4
  have hs5 : dist (z 5) (z 0) ^ 2 = 1 := D.side 5
  have ht0 : dist (z 0) (z 2) ^ 2 = 2 := D.twoStep 0
  have ht1 : dist (z 1) (z 3) ^ 2 = 2 := D.twoStep 1
  have ht2 : dist (z 2) (z 4) ^ 2 = 2 := D.twoStep 2
  have ht3 : dist (z 3) (z 5) ^ 2 = 2 := D.twoStep 3
  have ht4 : dist (z 4) (z 0) ^ 2 = 2 := D.twoStep 4
  have ht5 : dist (z 5) (z 1) ^ 2 = 2 := D.twoStep 5
  have ho0 : 3 ≤ dist (z 0) (z 3) ^ 2 := D.opposite 0
  have ho1 : 3 ≤ dist (z 1) (z 4) ^ 2 := D.opposite 1
  have ho2 : 3 ≤ dist (z 2) (z 5) ^ 2 := D.opposite 2
  have hq0 := CATZero.quadrilateral_saturation h (z 0) (z 1) (z 3) (z 4) 3 3
    ho0 ho1 (by rw [hs0, ht1, hs3, ht4]; norm_num)
  have hq1 := CATZero.quadrilateral_saturation h (z 1) (z 2) (z 4) (z 5) 3 3
    ho1 ho2 (by rw [hs1, ht2, hs4, ht5]; norm_num)
  have hd0 := hq0.1
  have hd1 := hq0.2.1
  have hd2 := hq1.2.1
  constructor
  · intro i j
    fin_cases i <;> fin_cases j
    · change dist (z 0) (z 0) ^ 2 = (0 : ℕ)
      simp
    · change dist (z 0) (z 1) ^ 2 = (1 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hs0
    · change dist (z 0) (z 2) ^ 2 = (2 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using ht0
    · change dist (z 0) (z 3) ^ 2 = (3 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hd0
    · change dist (z 0) (z 4) ^ 2 = (2 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using ht4
    · change dist (z 0) (z 5) ^ 2 = (1 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hs5
    · change dist (z 1) (z 0) ^ 2 = (1 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hs0
    · change dist (z 1) (z 1) ^ 2 = (0 : ℕ)
      simp
    · change dist (z 1) (z 2) ^ 2 = (1 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hs1
    · change dist (z 1) (z 3) ^ 2 = (2 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using ht1
    · change dist (z 1) (z 4) ^ 2 = (3 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hd1
    · change dist (z 1) (z 5) ^ 2 = (2 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using ht5
    · change dist (z 2) (z 0) ^ 2 = (2 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using ht0
    · change dist (z 2) (z 1) ^ 2 = (1 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hs1
    · change dist (z 2) (z 2) ^ 2 = (0 : ℕ)
      simp
    · change dist (z 2) (z 3) ^ 2 = (1 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hs2
    · change dist (z 2) (z 4) ^ 2 = (2 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using ht2
    · change dist (z 2) (z 5) ^ 2 = (3 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hd2
    · change dist (z 3) (z 0) ^ 2 = (3 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hd0
    · change dist (z 3) (z 1) ^ 2 = (2 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using ht1
    · change dist (z 3) (z 2) ^ 2 = (1 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hs2
    · change dist (z 3) (z 3) ^ 2 = (0 : ℕ)
      simp
    · change dist (z 3) (z 4) ^ 2 = (1 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hs3
    · change dist (z 3) (z 5) ^ 2 = (2 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using ht3
    · change dist (z 4) (z 0) ^ 2 = (2 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using ht4
    · change dist (z 4) (z 1) ^ 2 = (3 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hd1
    · change dist (z 4) (z 2) ^ 2 = (2 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using ht2
    · change dist (z 4) (z 3) ^ 2 = (1 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hs3
    · change dist (z 4) (z 4) ^ 2 = (0 : ℕ)
      simp
    · change dist (z 4) (z 5) ^ 2 = (1 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hs4
    · change dist (z 5) (z 0) ^ 2 = (1 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hs5
    · change dist (z 5) (z 1) ^ 2 = (2 : ℕ)
      simpa only [Nat.cast_ofNat, Nat.cast_one] using ht5
    · change dist (z 5) (z 2) ^ 2 = (3 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hd2
    · change dist (z 5) (z 3) ^ 2 = (2 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using ht3
    · change dist (z 5) (z 4) ^ 2 = (1 : ℕ)
      rw [dist_comm]
      simpa only [Nat.cast_ofNat, Nat.cast_one] using hs4
    · change dist (z 5) (z 5) ^ 2 = (0 : ℕ)
      simp
  · intro j
    fin_cases j
    · rfl
    · exact hq0.2.2.symm
    · exact hq1.2.2.symm.trans hq0.2.2.symm
    · exact CATZero.mid_swap h (z 0) (z 3)
    · exact (CATZero.mid_swap h (z 1) (z 4)).trans hq0.2.2.symm
    · exact (CATZero.mid_swap h (z 2) (z 5)).trans (hq1.2.2.symm.trans hq0.2.2.symm)

/-- The radius squared at the common opposite-pair midpoint. -/
theorem radius (D : MetricHexagon z) (h : CATZero X) (j : Fin 6) :
    dist (CATZero.mid h (z 0) (z 3)) (z j) ^ 2 = 3 / 4 := by
  obtain ⟨hd, hc⟩ := D.rigidity h
  rw [← hc j, dist_comm, CATZero.dist_left_mid, div_pow, hd, hexDistSq_opposite]
  norm_num

end MetricHexagon
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

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MetricHexagon
attribute [-instance] _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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

namespace HyperbolicObstruction
namespace MetricHexagon
variable {X : Type*} [MetricSpace X] {z : Fin 6 → X}

/-- Central log comparison is equality for every pair of hexagon vertices.
This proves the exact flatness used by the obstruction without assuming a
flat-sector theorem or treating the tangent cone as a vector space. -/
theorem log_dist (D : MetricHexagon z) (h : CATZero X) (i j : Fin 6) :
    dist (TangentCone.log h (CATZero.mid h (z 0) (z 3)) (z i))
      (TangentCone.log h (CATZero.mid h (z 0) (z 3)) (z j)) = dist (z i) (z j) := by
  let c := CATZero.mid h (z 0) (z 3)
  let T := TangentCone.coneData h c
  let L := TangentCone.log h c
  obtain ⟨hd, hc⟩ := D.rigidity h
  have hr (k : Fin 6) : dist c (z k) ^ 2 = 3 / 4 := D.radius h k
  have hop : T.Opposite (L (z j)) (L (z (j + 3))) := by
    have hh := TangentCone.opposite_mid_logs h (z j) (z (j + 3))
    rw [hc j] at hh
    exact hh
  have hupper := T.opposite_pairing (TangentCone.catZero h c) hop (L (z i))
  rw [T.pairing_comm (L (z j)), T.pairing_comm (L (z (j + 3)))] at hupper
  have hl := TangentCone.pairing_log_ge h c (z i) (z j)
  have hl' := TangentCone.pairing_log_ge h c (z i) (z (j + 3))
  have hsum : dist (z i) (z j) ^ 2 + dist (z i) (z (j + 3)) ^ 2 = 3 := by
    rw [hd, hd]
    exact_mod_cast hexDistSq_opposite_sum i j
  rw [hr i, hr j] at hl
  rw [hr i, hr (j + 3)] at hl'
  change (3 / 4 + 3 / 4 - dist (z i) (z j) ^ 2) / 2 ≤
    T.pairing (L (z i)) (L (z j)) at hl
  change (3 / 4 + 3 / 4 - dist (z i) (z (j + 3)) ^ 2) / 2 ≤
    T.pairing (L (z i)) (L (z (j + 3))) at hl'
  have hp : T.pairing (L (z i)) (L (z j)) =
      (3 / 2 - dist (z i) (z j) ^ 2) / 2 := by linarith
  have hn (k : Fin 6) : T.normSq (L (z k)) = 3 / 4 := by
    exact (TangentCone.normSq_log h c (z k)).trans (hr k)
  unfold ConeData.pairing at hp
  rw [hn i, hn j] at hp
  change dist (L (z i)) (L (z j)) = dist (z i) (z j)
  nlinarith [dist_nonneg (x := L (z i)) (y := L (z j)), dist_nonneg (x := z i) (y := z j)]

/-- Every central midpoint comparison in the core hexagon is an equality. -/
theorem central_mid (D : MetricHexagon z) (h : CATZero X) (i j : Fin 6) :
    dist (CATZero.mid h (z 0) (z 3)) (CATZero.mid h (z i) (z j)) ^ 2 =
      3 / 4 - (hexDistSq i j : ℝ) / 4 := by
  have he := TangentCone.cn_eq_of_log_dist h (CATZero.mid h (z 0) (z 3)) (z i) (z j)
    (D.log_dist h i j) (t := 1 / 2) (by norm_num)
  rw [D.radius h i, D.radius h j, (D.rigidity h).1 i j] at he
  change dist _ (CATZero.mid h (z i) (z j)) ^ 2 = _ at he
  linarith

end MetricHexagon
end HyperbolicObstruction


noncomputable section
namespace HyperbolicObstruction
namespace CoreGeometry
open IncidenceTemplate

def HexagonCode.vertices (H : HexagonCode) : Fin 6 → Vertex :=
  ![.inl H.a, .inr H.ab, .inl H.b, .inr H.bc, .inl H.c, .inr H.ca]

lemma centerPair_complete : ∀ r l, ¬Incident (pointOfRepresentative r) l →
    ∃ n : Fin 44, centerPair n = (r,l) := by
  decide

end CoreGeometry
end HyperbolicObstruction


noncomputable section
namespace HyperbolicObstruction
namespace CoreGeometry
open IncidenceTemplate

namespace MetricCore
variable {X : Type*}
  [MetricSpace X]
  {z : Vertex → X}

/-- A fixed actual opposite pair defines the common center. -/
def center (h : CATZero X) : X := CATZero.mid h (z (.inl 0)) (z (.inr 0))

end MetricCore
end CoreGeometry
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
namespace CoreGeometry

/-- The three-field, two-fractional-geodesic inequality in the source's
configuration proposition, at the exceptional missing incidence. -/
def ExceptionalTest {X : Type*} [MetricSpace X] (h : CATZero X) (z : Vertex → X) : Prop :=
  ∀ t ∈ Set.Ioc (0 : ℝ) 1,
    t ^ 2 * (1 / 2 + 1) ≤
      dist (CATZero.segment h (z (.inr 4)) (CATZero.mid h (z (.inl 2)) (z (.inl 9))) t)
        (CATZero.segment h (z (.inr 4)) (z (.inl 3)) t) ^ 2

end CoreGeometry
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

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Template
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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

lemma card_edges : Fintype.card Edge = 32 := by decide

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ColoredApex
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
variable {D : Type*} [DecidableEq D] [Fintype D]

namespace PictureMap
variable (c : D → Bool) (M : PictureMap D)

def apexCount : ℕ := Nat.card (Quotient ((SameCycle.setoid M.vertex).comap
  (Subtype.val : {x : D // c x = true} → D)))

def apexPerm (h : ∀ x, c (M.vertex x) = c x) : Perm {x : D // c x = true} :=
  M.vertex.subtypePerm (fun x => by rw [h x])

omit [DecidableEq D] in
lemma color_of_sameCycle (h : ∀ x, c (M.vertex x) = c x) {a b : D}
    (hab : M.vertex.SameCycle a b) : c a = c b := by
  exact (sameCycle_le_of_apply (s := Setoid.ker c) (fun x => (h x).symm)) hab

omit [DecidableEq D] in
lemma radial_far {a b : D} (h : ∀ x, c (M.vertex x) = c x)
    (ha : c a = true) (hb : c (M.edge b) = false) :
    ¬ M.vertex.SameCycle a (M.edge b) := by
  intro he
  have hc := M.color_of_sameCycle c h he
  rw [ha,hb] at hc
  exact Bool.noConfusion hc

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureGenus
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
variable {D : Type*} [DecidableEq D] [Fintype D]

namespace PictureMap
variable (M : PictureMap D)

omit [Fintype D] in
lemma switch_edge_a (a b : D)
    (hfar : ¬ M.vertex.SameCycle a (M.edge b)) :
    (M.switch a b).edge a = M.edge b := by
  have ha : M.edge b ≠ a := fun he => hfar (he.symm.sameCycle M.vertex)
  simp only [switch,mul_apply,swap_apply_left,
    swap_apply_of_ne_of_ne ha (M.edge_ne b)]

omit [Fintype D] in
lemma switch_edge_b (a b : D) (hv : M.vertex.SameCycle a b)
    (hfar : ¬ M.vertex.SameCycle a (M.edge a)) :
    (M.switch a b).edge b = M.edge a := by
  have hb : M.edge a ≠ b := fun he => hfar (he.symm ▸ hv)
  simp only [switch,mul_apply,swap_apply_right,
    swap_apply_of_ne_of_ne (M.edge_ne a) hb]

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MappedPicture
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
variable {D : Type*} [DecidableEq D] [Fintype D]

namespace PictureMap

instance instFinite : Finite (PictureMap D) :=
  Finite.of_injective (fun M : PictureMap D => (M.face,M.edge))
    (fun _ _ h => PictureMap.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConditionalStar
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
noncomputable section
noncomputable section
open Filter Topology
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Filter Topology

namespace HyperbolicObstruction

/-- Actual normalized orbit points along a symmetric finite generator list. -/
structure EnergyOrbit (L X : Type*) [Fintype L] [MetricSpace X] (M : ℝ) where
  cat : CATZero X
  base : X
  isom : L → X ≃ᵢ X
  inverse : L ≃ L
  symmetric : ∀ i, isom (inverse i) = (isom i).symm
  minimum : ∀ y : X, (∑ i, dist base (isom i base) ^ 2) ≤ ∑ i, dist y (isom i y) ^ 2
  energy : (𝔼 i, dist base (isom i base) ^ 2) = 1
  bound : ∀ i, dist base (isom i base) ≤ M

namespace EnergyOrbit
variable {L X : Type*} [Fintype L] [MetricSpace X] {M : ℝ} (O : EnergyOrbit L X M)

abbrev Cone := TangentCone O.cat O.base
abbrev cone : ConeData O.Cone := TangentCone.coneData O.cat O.base

def vector (i : L) : O.Cone := TangentCone.log O.cat O.base (O.isom i O.base)

end EnergyOrbit

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
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Graph
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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

variable {a b : Vertex}
lemma endpoints_pos (s : Step a b) (h : s.forward = true) : source s.field = a ∧ target s.field = b := by
  simpa only [h, Bool.true_eq, ↓reduceIte] using s.endpoints
lemma endpoints_neg (s : Step a b) (h : s.forward = false) : target s.field = a ∧ source s.field = b := by
  simpa only [h, Bool.false_eq_true, ↓reduceIte] using s.endpoints
end Step

lemma first_field (τ : TwoPath) : (first τ).field = .inl τ.val.1 := rfl
lemma second_field (τ : TwoPath) : (second τ).field = .inl τ.val.2 := rfl

end MasterGraph
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
namespace FiniteLaw
variable {α : Type*} [Fintype α]

lemma expect_abs_sub_le (μ : FiniteLaw α) (f : α → ℝ) :
    μ.expect (fun a => |f a - μ.expect f|) ≤ Real.sqrt (μ.variance f) := by
  simpa only [sq_abs, variance] using μ.expect_le_sqrt (fun a => |f a - μ.expect f|)

lemma markov (μ : FiniteLaw α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) {c : ℝ}
    (hc : 0 < c) : μ.prob (fun a => c ≤ f a) ≤ μ.expect f / c := by
  classical
  apply (le_div_iff₀ hc).mpr
  rw [prob]
  calc
    _ = μ.expect (fun a => c * if c ≤ f a then 1 else 0) := by
      rw [μ.expect_mul]; ring
    _ ≤ μ.expect f := μ.expect_mono fun a => by
      split_ifs with h <;> simp_all

end FiniteLaw

end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Normalization
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
namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

/-- Normalization of nonnegative counts. Positivity is proved before this
construction is used to form the uniform present-star law. -/
def normalize (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (hz : 0 < ∑ a, f a) : FiniteLaw α where
  mass a := f a / ∑ a, f a
  nonneg a := div_nonneg (hf a) hz.le
  sum_one := by rw [← Finset.sum_div]; exact div_self (ne_of_gt hz)

/-- The exact deterministic normalization estimate
for branch fibers and for ordered-distinct leaf fibers. -/
theorem normalize_uniform_bound [Nonempty α] (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hz : 0 < ∑ a, f a) (c : ℝ) :
    (normalize f hf hz).totalVariation uniform ≤ (∑ a, |f a - c|) / ∑ a, f a := by
  let Z : ℝ := ∑ a, f a
  let n : ℝ := Fintype.card α
  have hn : 0 < n := by dsimp [n]; exact_mod_cast Fintype.card_pos (α := α)
  have hZ : 0 < Z := hz
  have hpoint (a : α) : |f a / Z - 1 / n| ≤ |f a - c| / Z + |c / Z - 1 / n| := by
    calc
      _ = |(f a - c) / Z + (c / Z - 1 / n)| := by congr 1; ring
      _ ≤ |(f a - c) / Z| + |c / Z - 1 / n| := abs_add_le _ _
      _ = _ := by rw [abs_div,abs_of_pos hZ]
  have hc : n * |c / Z - 1 / n| = |Z - n * c| / Z := by
    have he : n * (c / Z - 1 / n) = -(Z - n * c) / Z := by field_simp; ring
    calc
      _ = |n * (c / Z - 1 / n)| := by rw [abs_mul,abs_of_pos hn]
      _ = _ := by rw [he,abs_div,abs_of_pos hZ,abs_neg]
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hpoint a)
  rw [Finset.sum_add_distrib,← Finset.sum_div,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  change (∑ a, |f a / Z - 1 / n|) ≤ (∑ a, |f a - c|) / Z + n * |c / Z - 1 / n| at hs
  rw [hc] at hs
  have he := (div_le_div_of_nonneg_right (abs_sum_sub_const f c) hZ.le)
  change |Z - n * c| / Z ≤ (∑ a, |f a - c|) / Z at he
  unfold totalVariation normalize uniform
  change (∑ a, |f a / Z - 1 / n|) / 2 ≤ _
  linarith

lemma totalVariation_triangle (μ ν κ : FiniteLaw α) :
    μ.totalVariation κ ≤ μ.totalVariation ν + ν.totalVariation κ := by
  unfold totalVariation
  rw [← add_div,← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact Finset.sum_le_sum fun a _ => abs_sub_le _ _ _

lemma totalVariation_map_le (μ ν : FiniteLaw α) (f : α → β) :
    (μ.map f).totalVariation (ν.map f) ≤ μ.totalVariation ν := by
  classical
  unfold totalVariation map
  apply div_le_div_of_nonneg_right _ (by norm_num)
  simp only [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ b, ∑ a, |(if f a = b then μ.mass a else 0) - (if f a = b then ν.mass a else 0)| := by
      exact Finset.sum_le_sum fun b _ => Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single (f a)]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp

lemma map_map {γ : Type*} [Fintype γ] (μ : FiniteLaw α) (f : α → β) (g : β → γ) :
    (μ.map f).map g = μ.map (g ∘ f) := by
  classical
  apply FiniteLaw.ext
  funext c
  unfold map
  simp only
  have hi (b : β) : (if g b = c then ∑ a, if f a = b then μ.mass a else 0 else 0) =
      ∑ a, if g b = c then (if f a = b then μ.mass a else 0) else 0 := by
    by_cases h : g b = c <;> simp [h]
  simp_rw [hi]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  have hj (b : β) : (if g b = c then (if f a = b then μ.mass a else 0) else 0) =
      (if f a = b then (if g (f a) = c then μ.mass a else 0) else 0) := by
    by_cases h : f a = b
    · subst b; simp
    · simp [h]
  simp_rw [hj]
  simp

lemma expect_abs_sub_le_relative (μ : FiniteLaw α) (f : α → ℝ) {r : ℝ}
    (hr : 0 ≤ r) (hm : 0 ≤ μ.expect f) (hv : μ.variance f ≤ r * μ.expect f ^ 2) :
    μ.expect (fun a => |f a - μ.expect f|) ≤ Real.sqrt r * μ.expect f := by
  calc
    _ ≤ Real.sqrt (μ.variance f) := μ.expect_abs_sub_le f
    _ ≤ Real.sqrt (r * μ.expect f ^ 2) := Real.sqrt_le_sqrt hv
    _ = _ := by rw [Real.sqrt_mul hr,Real.sqrt_sq hm]

end FiniteLaw
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FiberLaw
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
namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

lemma uniform_map_mass [Nonempty α] (f : α → β) (b : β) :
    ((uniform : FiniteLaw α).map f).mass b = (Fintype.card {a // f a = b} : ℝ) / Fintype.card α := by
  classical
  unfold map uniform
  simp only
  have hi (a : α) : (if f a = b then 1 / (Fintype.card α : ℝ) else 0) =
      (if f a = b then (1 : ℝ) else 0) / Fintype.card α := by split_ifs <;> simp
  simp_rw [hi]
  rw [← Finset.sum_div]
  congr 1
  simp [Fintype.card_subtype]

lemma uniform_map_eq_normalize [Nonempty α] (f : α → β) :
    (uniform : FiniteLaw α).map f =
      normalize (fun b => (Fintype.card {a // f a = b} : ℝ)) (fun _ => Nat.cast_nonneg _)
        (by rw [← Nat.cast_sum,card_fibers]; exact_mod_cast Fintype.card_pos (α := α)) := by
  apply ext
  funext b
  simp only [uniform_map_mass,normalize,← Nat.cast_sum,card_fibers]

lemma uniform_map_bound [Nonempty α] [Nonempty β] (f : α → β) (c : ℝ) :
    ((uniform : FiniteLaw α).map f).totalVariation uniform ≤
      (∑ b, |(Fintype.card {a // f a = b} : ℝ) - c|) / Fintype.card α := by
  rw [uniform_map_eq_normalize]
  simpa only [← Nat.cast_sum,card_fibers] using
    normalize_uniform_bound (fun b => (Fintype.card {a // f a = b} : ℝ)) (fun _ => Nat.cast_nonneg _)
      (by rw [← Nat.cast_sum,card_fibers]; exact_mod_cast Fintype.card_pos (α := α)) c

/-- The uniform law on a subset, included in the ambient finite set, differs
from the ambient uniform law by exactly the proportion excluded. -/
lemma uniform_subtype_tv [Nonempty α] (P : α → Prop) [DecidablePred P] [Nonempty {a // P a}] :
    ((uniform : FiniteLaw {a // P a}).map Subtype.val).totalVariation (uniform : FiniteLaw α) =
      1 - (Fintype.card {a // P a} : ℝ) / Fintype.card α := by
  classical
  let m : ℝ := Fintype.card {a // P a}
  let n : ℝ := Fintype.card α
  have hm : 0 < m := by dsimp [m]; exact_mod_cast Fintype.card_pos
  have hn : 0 < n := by dsimp [n]; exact_mod_cast Fintype.card_pos
  have hmn : m ≤ n := by dsimp [m,n]; exact_mod_cast Fintype.card_subtype_le P
  have hrec : 1 / n ≤ 1 / m := one_div_le_one_div_of_le hm hmn
  have hmass (a : α) : ((uniform : FiniteLaw {a // P a}).map Subtype.val).mass a =
      if P a then 1 / m else 0 := by
    unfold map uniform
    dsimp only
    by_cases ha : P a
    · rw [Finset.sum_eq_single ⟨a,ha⟩]
      · simp [ha,m]
      · intro b _ hb; simp [show b.val ≠ a by intro hh; exact hb (Subtype.ext hh)]
      · simp
    · simp [ha,show ∀ b : {a // P a}, b.val ≠ a by intro b h; exact ha (h ▸ b.property)]
  unfold totalVariation
  simp_rw [hmass]
  change (∑ a, |(if P a then 1 / m else 0) - 1 / n|) / 2 = _
  have hi (a : α) : |(if P a then 1 / m else 0) - 1 / n| =
      (if P a then 1 / m - 2 / n else 0) + 1 / n := by
    split_ifs
    · rw [abs_of_nonneg (sub_nonneg.mpr hrec)]; ring
    · rw [zero_sub,abs_neg,abs_of_pos (one_div_pos.mpr hn)]; ring
  simp_rw [hi]
  rw [Finset.sum_add_distrib]
  have hs : (∑ a : α, if P a then 1 / m - 2 / n else 0) = m * (1 / m - 2 / n) := by
    simp [← Finset.sum_filter,Fintype.card_subtype,m]
    ring
  rw [hs]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  change (m * (1 / m - 2 / n) + n * (1 / n)) / 2 = 1 - m / n
  field_simp
  ring

end FiniteLaw
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Chernoff
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
namespace FiniteLaw
variable {α : Type*} [Fintype α]

lemma prob_or_le (μ : FiniteLaw α) (E F : α → Prop) [DecidablePred E] [DecidablePred F] :
    μ.prob (fun a => E a ∨ F a) ≤ μ.prob E + μ.prob F := by
  rw [prob, prob, prob, ← μ.expect_add]
  apply μ.expect_mono
  intro a
  by_cases he : E a <;> by_cases hf : F a <;> simp [he,hf]

lemma centeredCount_mgf {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (S : Finset I) {t : ℝ} (ht : |t| ≤ 1) :
    (bernoulliProduct p hp).expect (fun w => Real.exp (t*centeredCount p S w)) ≤
      Real.exp ((∑ i ∈ S, p i)*t^2) := by
  classical
  have hx (w : I → Bool) : Real.exp (t*centeredCount p S w) =
      ∏ i, Real.exp (t*(if i ∈ S then (if w i then (1:ℝ) else 0)-p i else 0)) := by
    rw [← Real.exp_sum]
    congr 1
    simp only [centeredCount,Finset.mul_sum,mul_ite,mul_zero]
    simp only [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]
  simp_rw [hx]
  rw [bernoulliProduct_expect_product p hp
    (fun i (b : Bool) => Real.exp (t*(if i ∈ S then (if b then (1:ℝ) else 0)-p i else 0)))]
  calc
    _ ≤ ∏ i, Real.exp (if i ∈ S then p i*t^2 else 0) := by
      apply Finset.prod_le_prod
      · intro i _
        exact add_nonneg (mul_nonneg (sub_nonneg.mpr (hp i).2) (Real.exp_pos _).le)
          (mul_nonneg (hp i).1 (Real.exp_pos _).le)
      · intro i _
        by_cases hi : i ∈ S
        · simpa [hi] using bernoulli_centered_exp_le (hp i) ht
        · simp [hi]
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp [Finset.sum_mul]

/-- Two-sided multiplicative Chernoff estimate, with an explicit constant 4.
It suffices for the simultaneous six-letter pair counts. -/
theorem centeredCount_chernoff {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (S : Finset I)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 2) :
    (bernoulliProduct p hp).prob (fun w => ε*(∑ i ∈ S, p i) ≤ |centeredCount p S w|) ≤
      2*Real.exp (-ε^2*(∑ i ∈ S, p i)/4) := by
  classical
  let μ := bernoulliProduct p hp
  let m := ∑ i ∈ S, p i
  let t := ε/2
  have ht : 0 < t := half_pos hε
  have ht1 : t ≤ 1 := by dsimp [t]; linarith
  have htail (s : ℝ) (hs : |s| = t) :
      μ.prob (fun w => t*ε*m ≤ s*centeredCount p S w) ≤ Real.exp (-ε^2*m/4) := by
    have hh := μ.markov (fun w => Real.exp (s*centeredCount p S w))
      (fun _ => (Real.exp_pos _).le) (Real.exp_pos (t*ε*m))
    have hm := centeredCount_mgf p hp S (show |s| ≤ 1 by rw [hs]; exact ht1)
    have hsq : s^2 = t^2 := by rw [← sq_abs,hs]
    have he : μ.prob (fun w => t*ε*m ≤ s*centeredCount p S w) =
        μ.prob (fun w => Real.exp (t*ε*m) ≤ Real.exp (s*centeredCount p S w)) := by
      congr 1; funext w; exact propext Real.exp_le_exp.symm
    rw [he]
    apply hh.trans
    apply (div_le_div_of_nonneg_right hm (Real.exp_pos _).le).trans
    rw [← Real.exp_sub,hsq]
    apply le_of_eq
    congr 1
    dsimp [t,m]
    ring
  have hu := htail t (abs_of_pos ht)
  have hl := htail (-t) (by rw [abs_neg,abs_of_pos ht])
  have hh : μ.prob (fun w => ε*m ≤ |centeredCount p S w|) ≤
      μ.prob (fun w => t*ε*m ≤ t*centeredCount p S w ∨ t*ε*m ≤ -t*centeredCount p S w) := by
    apply μ.prob_mono
    intro w hw
    rcases le_abs.mp hw with h | h
    · left; nlinarith
    · right; nlinarith
  exact hh.trans ((μ.prob_or_le _ _).trans (by linarith))

end FiniteLaw
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Conditioning
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
namespace FiniteLaw
variable {I : Type*} [DecidableEq I]

variable [Fintype I]

lemma bernoulliProduct_mass_join (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset I) (a : S → Bool) (b : {i : I // i ∉ S} → Bool) :
    (bernoulliProduct p hp).mass (joinTables S a b) =
      (bernoulliProduct (fun i : S => p i.val) (fun i => hp i.val)).mass a *
      (bernoulliProduct (fun i : {i : I // i ∉ S} => p i.val) (fun i => hp i.val)).mass b := by
  change (∏ i, if joinTables S a b i then p i else 1 - p i) = _
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ S)]
  simp only [joinTables_in,joinTables_out,bernoulliProduct]
  congr 1
  apply Finset.prod_congr (by ext; simp)
  intros
  rfl

lemma bernoulliProduct_expect_split (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset I) (f : (I → Bool) → ℝ) :
    (bernoulliProduct p hp).expect f =
      (bernoulliProduct (fun i : S => p i.val) (fun i => hp i.val)).expect (fun a =>
        (bernoulliProduct (fun i : {i : I // i ∉ S} => p i.val) (fun i => hp i.val)).expect
          (fun b => f (joinTables S a b))) := by
  unfold expect
  rw [← (Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => Bool)).symm.sum_comp
    (fun w => (bernoulliProduct p hp).mass w * f w),Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  change (bernoulliProduct p hp).mass (joinTables S a b) * f (joinTables S a b) = _
  rw [bernoulliProduct_mass_join]
  ring

/-- Exact independence of an arbitrary outside-trial statistic from the event
that every trial in S is present. -/
theorem bernoulliProduct_event_mul (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset I) (f : (I → Bool) → ℝ)
    (depends : ∀ w z, (∀ i, i ∉ S → w i = z i) → f w = f z) :
    (bernoulliProduct p hp).expect (fun w => if ∀ i ∈ S, w i = true then f w else 0) =
      (∏ i ∈ S, p i) * (bernoulliProduct p hp).expect f := by
  let μ₁ := bernoulliProduct (fun i : S => p i.val) (fun i => hp i.val)
  let μ₂ := bernoulliProduct (fun i : {i : I // i ∉ S} => p i.val) (fun i => hp i.val)
  let g (b : {i : I // i ∉ S} → Bool) := f (joinTables S (fun _ => true) b)
  have hf (a : S → Bool) (b : {i : I // i ∉ S} → Bool) : f (joinTables S a b) = g b := by
    apply depends
    intro i hi
    exact (joinTables_out S a b ⟨i,hi⟩).trans (joinTables_out S (fun _ => true) b ⟨i,hi⟩).symm
  have he (a : S → Bool) (b : {i : I // i ∉ S} → Bool) :
      (∀ i ∈ S, joinTables S a b i = true) ↔ ∀ i, a i = true := by
    constructor
    · intro h i
      simpa only [joinTables_in] using h i.val i.property
    · intro h i hi
      exact (joinTables_in S a b ⟨i,hi⟩).trans (h ⟨i,hi⟩)
  have hmean : (bernoulliProduct p hp).expect f = μ₂.expect g := by
    rw [bernoulliProduct_expect_split p hp S]
    simp only [hf]
    exact μ₁.expect_const _
  have hprob : μ₁.expect (fun a => if ∀ i, a i = true then (1 : ℝ) else 0) = ∏ i ∈ S, p i := by
    have h := bernoulliProduct_all p hp S
    rw [bernoulliProduct_expect_split p hp S] at h
    simp only [he] at h
    simp only [expect_const] at h
    exact h
  rw [bernoulliProduct_expect_split p hp S,hmean]
  simp only [hf,he]
  have hs : ∀ a : S → Bool,
      μ₂.expect (fun b => if ∀ i, a i = true then g b else 0) =
      (if ∀ i, a i = true then (1 : ℝ) else 0) * μ₂.expect g := by
    intro a
    split_ifs <;> simp [expect_const]
  change μ₁.expect (fun a => μ₂.expect (fun b => if ∀ i, a i = true then g b else 0)) = _
  simp_rw [hs]
  calc
    _ = μ₁.expect (fun a => μ₂.expect g * (if ∀ i, a i = true then (1 : ℝ) else 0)) := by
      congr 1; funext a; ring
    _ = μ₂.expect g * μ₁.expect (fun a => if ∀ i, a i = true then (1 : ℝ) else 0) := μ₁.expect_mul _ _
    _ = _ := by rw [hprob]; ring

end FiniteLaw
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StarError
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
namespace FiniteLaw
variable {α : Type*} [Fintype α]
lemma expect_div (μ : FiniteLaw α) (f : α → ℝ) (c : ℝ) :
    μ.expect (fun a => f a / c) = μ.expect f / c := by
  simp only [expect, mul_div_assoc, Finset.sum_div]

lemma exists_lt_of_expect_lt (μ : FiniteLaw α) (f : α → ℝ) (t : ℝ)
    (h : μ.expect f < t) : ∃ a, f a < t := by
  by_contra! hn
  have hh := μ.expect_mono hn
  rw [μ.expect_const] at hh
  exact (not_lt_of_ge hh) h
end FiniteLaw

end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FiniteSelection
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
namespace FiniteLaw
variable {α β J : Type*} [Fintype α] [Fintype β] [Fintype J]

/-- All finite tests and any additional table event can be imposed at once.
The only premise is the actual expectation/probability estimate, not the
existence of a good table. -/
theorem exists_good_simultaneously (μ : FiniteLaw α) (f : J → α → ℝ)
    (hf : ∀ j a, 0 ≤ f j a) (bad : α → Prop) [DecidablePred bad]
    {ε : ℝ} (hε : 0 < ε)
    (h : (∑ j, μ.expect (f j)) + ε*μ.prob bad < ε) :
    ∃ a, ¬bad a ∧ ∀ j, f j a < ε := by
  let F (a : α) := (∑ j, f j a) + ε*(if bad a then 1 else 0)
  have he : μ.expect F < ε := by
    dsimp [F]
    rw [μ.expect_add,μ.expect_sum,μ.expect_mul]
    exact h
  obtain ⟨a,ha⟩ := μ.exists_lt_of_expect_lt F ε he
  have hs : 0 ≤ ∑ j, f j a := Finset.sum_nonneg fun j _ => hf j a
  have hb : ¬bad a := by
    intro hb
    dsimp [F] at ha
    simp only [hb,↓reduceIte,mul_one] at ha
    linarith
  refine ⟨a,hb,fun j => ?_⟩
  have hj : f j a ≤ ∑ j, f j a :=
    Finset.single_le_sum (fun j _ => hf j a) (Finset.mem_univ j)
  have hind : 0 ≤ ε * (if bad a then 1 else 0) :=
    mul_nonneg hε.le (by split_ifs; norm_num)
  exact (hj.trans (le_add_of_nonneg_right hind)).trans_lt ha

/-- Product law for the independent master and six-letter arrays. -/
def prod (μ : FiniteLaw α) (ν : FiniteLaw β) : FiniteLaw (α × β) where
  mass a := μ.mass a.1 * ν.mass a.2
  nonneg a := mul_nonneg (μ.nonneg _) (ν.nonneg _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum,ν.sum_one,mul_one]
    exact μ.sum_one

lemma expect_prod (μ : FiniteLaw α) (ν : FiniteLaw β) (f : α × β → ℝ) :
    (μ.prod ν).expect f = μ.expect (fun a => ν.expect (fun b => f (a,b))) := by
  unfold expect prod
  simp only [Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma expect_prod_fst (μ : FiniteLaw α) (ν : FiniteLaw β) (f : α → ℝ) :
    (μ.prod ν).expect (fun a => f a.1) = μ.expect f := by
  rw [expect_prod]
  simp only [expect_const]

lemma expect_prod_snd (μ : FiniteLaw α) (ν : FiniteLaw β) (f : β → ℝ) :
    (μ.prod ν).expect (fun a => f a.2) = ν.expect f := by
  rw [expect_prod]
  change μ.expect (fun _ => ν.expect f) = _
  exact μ.expect_const _

end FiniteLaw
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Distinct
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
namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]

omit [DecidableEq α] in
lemma map_uniform_equiv [Nonempty α] [Nonempty β] (e : α ≃ β) :
    (uniform : FiniteLaw α).map e = (uniform : FiniteLaw β) := by
  classical
  apply ext
  funext b
  unfold map uniform
  dsimp only
  rw [Finset.sum_eq_single (e.symm b)]
  · simp [Fintype.card_congr e]
  · intro a _ ha
    simp [show e a ≠ b by intro h; exact ha (e.injective (h.trans (e.apply_symm_apply b).symm))]
  · simp

lemma distinct_tv [Nonempty β] [Nonempty (α ↪ β)] :
    ((uniform : FiniteLaw (α ↪ β)).map (fun f : α ↪ β => (f : α → β))).totalVariation
      (uniform : FiniteLaw (α → β)) =
      1 - ((Fintype.card β).descFactorial (Fintype.card α) : ℝ) /
        (Fintype.card β : ℝ) ^ Fintype.card α := by
  classical
  let e : (α ↪ β) ≃ {f : α → β // Function.Injective f} := embeddingSubtypeEquiv
  let : Nonempty {f : α → β // Function.Injective f} :=
    ⟨e (Classical.choice inferInstance)⟩
  have hh : (uniform : FiniteLaw (α ↪ β)).map (fun f : α ↪ β => (f : α → β)) =
      (uniform : FiniteLaw {f : α → β // Function.Injective f}).map Subtype.val := by
    rw [← map_uniform_equiv e,map_map]
    rfl
  rw [hh,uniform_subtype_tv]
  have hc : Fintype.card {f : α → β // Function.Injective f} =
      (Fintype.card β).descFactorial (Fintype.card α) :=
    (Fintype.card_congr e).symm.trans Fintype.card_embedding_eq
  simp only [hc,Fintype.card_fun,Nat.cast_pow]

end FiniteLaw
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_DipoleSwitch
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
variable {D I L V : Type*}
namespace PictureMap

variable (M : PictureMap D) {q : Perm I} {a b : I → D}

lemma paired_reverse {i : I} (h : M.edge (a i) = b i) : M.edge (b i) = a i := by
  rw [← h,M.edge_edge]

lemma dipole_sameVertex (hF : OppositeFaces M.face q a b) {i : I}
    (hp : M.edge (a i) = b i) :
    M.vertex.SameCycle (a (q i)) (M.edge (b (q i))) := by
  have hy : M.vertex (M.edge (b (q i))) = b i := by
    change M.face (M.edge (M.edge (b (q i)))) = b i
    rw [M.edge_edge,hF.b_face]
  have hx : M.vertex (b i) = a (q i) := by
    change M.face (M.edge (b i)) = a (q i)
    rw [M.paired_reverse hp,hF.a_face]
  have hh : M.vertex.SameCycle (M.edge (b (q i)))
      (M.vertex (M.vertex (M.edge (b (q i))))) := SameCycle.rfl.apply_right.apply_right
  rw [hy,hx] at hh
  exact hh.symm

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_DipoleRemove
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
variable {D I : Type*}
namespace PictureMap

namespace OppositeFaces
variable {f : Perm D} {q : Perm I} {a b : I → D} (h : OppositeFaces f q a b)
include h

lemma a_sameCycle [Fintype I] (i j : I) : f.SameCycle (a i) (a j) := by
  have hh : SameCycle.setoid q ≤ (SameCycle.setoid f).comap a := by
    apply sameCycle_le_of_apply
    intro k
    change f.SameCycle (a k) (a (q k))
    rw [← h.a_face]
    exact SameCycle.rfl.apply_right
  exact hh (h.cyclic i j)

lemma b_sameCycle [Fintype I] (i j : I) : f.SameCycle (b i) (b j) := by
  have hh : SameCycle.setoid q ≤ (SameCycle.setoid f).comap b := by
    apply sameCycle_le_of_apply
    intro k
    change f.SameCycle (b k) (b (q k))
    rw [← h.b_face]
    exact SameCycle.rfl.apply_left
  exact hh (h.cyclic i j)

end OppositeFaces
variable (M : PictureMap D) {q : Perm I} {a b : I → D}

lemma inDipole_edge (hp : ∀ i, M.edge (a i) = b i) (x : D) :
    InDipole a b (M.edge x) ↔ InDipole a b x := by
  have hfwd : ∀ x, InDipole a b x → InDipole a b (M.edge x) := by
    intro x hx
    rcases hx with ⟨i,rfl⟩ | ⟨i,rfl⟩
    · exact Or.inr ⟨i,(hp i).symm⟩
    · exact Or.inl ⟨i,(M.paired_reverse (hp i)).symm⟩
  constructor
  · intro hx
    simpa only [M.edge_edge] using hfwd (M.edge x) hx
  · exact hfwd x

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_DipoleChain
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
variable {D A : Type*} [DecidableEq D] [Fintype D] [AddCommMonoid A]

/-- The total lifted cellular chain (or any additive face statistic). A face
is counted once, independent of its number of independently indexed sides. -/
def faceChain (f : Perm D) (w : D → A) (hw : ∀ x, w (f x) = w x) : A :=
  classSum (SameCycle.setoid f) w (sameCycle_le_of_apply (s := Setoid.ker w) (fun x => (hw x).symm))

omit [DecidableEq D] in
lemma faceChain_subtype (f : Perm D) (w : D → A) (hw : ∀ x, w (f x) = w x)
    (P : D → Prop) (hp : ∀ x, P (f x) ↔ P x) :
    faceChain (f.subtypePerm hp) (w ∘ Subtype.val) (fun x => hw x.val) =
      classSum ((SameCycle.setoid f).comap (Subtype.val : Subtype P → D)) (w ∘ Subtype.val)
        (fun _ _ h => (sameCycle_le_of_apply (s := Setoid.ker w) (fun x => (hw x).symm)) h) := by
  have hs : SameCycle.setoid (f.subtypePerm hp) =
      (SameCycle.setoid f).comap (Subtype.val : Subtype P → D) := by
    ext x y; exact sameCycle_subtypePerm_iff f hp x y
  unfold faceChain
  congr 1

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonTarget
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

namespace CellTarget
variable {S L V A D : Type*} [AddCommMonoid A]
variable (T : CellTarget S L V A)

/-- For genuine closed target cell boundaries, vertex-map compatibility
follows from indexed face maps and the literal opposite-edge labels. -/
theorem respects_of_edge (M : PictureMap D) (j : D → S)
    (hj : IndexedFaceMap M.face T.next j)
    (he : ∀ x, T.edge (j (M.edge x)) = T.rev (T.edge (j x))) :
    M.Respects (T.edge ∘ j) T.start T.rev := by
  constructor
  · intro x
    change T.start (T.edge (j (M.face (M.edge x)))) = T.start (T.edge (j x))
    rw [hj.commute,T.next_start,he,T.rev_rev]
  · exact he

end CellTarget
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FaceWalk
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
variable {D C V : Type*} [DecidableEq D] [Fintype D]
namespace PictureMap

omit [DecidableEq D] in
lemma kind_cycle {M : PictureMap D} {kind : D → C} (hk : M.FaceKind kind)
    {a b : D} (h : M.face.SameCycle a b) : kind a = kind b := by
  exact (sameCycle_le_of_apply (s := Setoid.ker kind) (fun x => (hk x).symm)) h

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkCell
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

attribute [instance] WalkPicture.finite WalkPicture.decEq

namespace WalkPicture
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

def chain : A := ∑ x : P.Dart, T.weight (P.index x)
def Reduced : Prop := ∀ a, T.free (T.kind (P.index a)) = true →
  P.index (P.pairing.edge a) ≠ T.opposite (P.index a)

/-- Retain every individual surviving step and EVERY frozen face. Only free
cone steps may disappear; on frozen faces the original cyclic indexing is
retained exactly, not just up to a word or a chain class. -/
structure Retains (Q : WalkPicture.{u} T) where
  map : Q.Dart → P.Dart
  injective : Function.Injective map
  index : ∀ x, Q.index x = P.index (map x)
  face : ∀ x, T.free (T.kind (Q.index x)) = false →
    map (Q.pairing.face x) = P.pairing.face (map x)
  complete : ∀ x, T.free (T.kind (P.index x)) = false → ∃ y, map y = x

def Retains.trans {Q R : WalkPicture.{u} T} (hPQ : P.Retains Q) (hQR : Q.Retains R) :
    P.Retains R := by
  refine ⟨hPQ.map ∘ hQR.map,hPQ.injective.comp hQR.injective,?_,?_,?_⟩
  · intro x; exact (hQR.index x).trans (hPQ.index (hQR.map x))
  · intro x hx
    change hPQ.map (hQR.map (R.pairing.face x)) = _
    rw [hQR.face x hx]
    exact hPQ.face (hQR.map x) (by rw [← hQR.index]; exact hx)
  · intro x hx
    obtain ⟨y,hy⟩ := hPQ.complete x hx
    obtain ⟨z,hz⟩ := hQR.complete y (by rw [hPQ.index,hy]; exact hx)
    exact ⟨z,by simp only [Function.comp_apply,hz,hy]⟩

lemma nonmonogon {x : P.Dart} (hx : T.free (T.kind (P.index x)) = true) :
    P.pairing.face x ≠ x := by
  intro he
  have hc := P.closed x
  change T.front (P.index (P.pairing.face x)) = T.back (P.index x) at hc
  rw [he] at hc
  exact T.loopless (P.index x) hx hc

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FrozenWalk
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

/-- Retain every surviving step, without changing any surviving frozen face.
Unlike the stronger `Retains`, this permits cancellation of entire frozen
faces. Protected outside faces will be retained separately at that boundary. -/
structure Survives (Q : WalkPicture.{u} T) where
  map : Q.Dart → P.Dart
  injective : Function.Injective map
  index : ∀ x, Q.index x = P.index (map x)
  face : ∀ x, T.free (T.kind (Q.index x)) = false →
    map (Q.pairing.face x) = P.pairing.face (map x)

variable {P}
def Retains.survives {Q : WalkPicture.{u} T} (h : P.Retains Q) : P.Survives Q :=
  ⟨h.map,h.injective,h.index,h.face⟩

variable (P)

def Survives.trans {Q R : WalkPicture.{u} T} (hPQ : P.Survives Q) (hQR : Q.Survives R) :
    P.Survives R := by
  refine ⟨hPQ.map ∘ hQR.map,hPQ.injective.comp hQR.injective,?_,?_⟩
  · intro x; exact (hQR.index x).trans (hPQ.index (hQR.map x))
  · intro x hx
    change hPQ.map (hQR.map (R.pairing.face x)) = _
    rw [hQR.face x hx]
    exact hPQ.face (hQR.map x) (by rw [← hQR.index]; exact hx)

lemma Survives.frozenMapped {Q : WalkPicture.{u} T} (h : P.Survives Q)
    (B : FrozenTarget T) (hm : P.FrozenMapped B) : Q.FrozenMapped B := by
  let j : Q.FrozenDart → P.FrozenDart := fun x =>
    ⟨h.map x.val,by rw [← h.index]; exact x.property⟩
  have hj : ∀ x, j (Q.frozenFace x) = P.frozenFace (j x) := by
    intro x; apply Subtype.ext; exact h.face x.val x.property
  constructor
  · intro x
    change Q.index (Q.pairing.face x.val) = B.next (Q.index x.val)
    rw [h.index,h.face x.val x.property,h.index x.val]
    exact hm.commute (j x)
  · intro x y hxy he
    apply Subtype.ext
    apply h.injective
    have hh := hm.injective (semiconj_perm_sameCycle hj hxy)
    apply congrArg Subtype.val (hh ?_)
    change P.index (h.map x.val) = P.index (h.map y.val)
    rw [← h.index,← h.index]
    exact he

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_EdgeMerge
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
variable {D : Type*}
namespace PictureMap
variable (M : PictureMap D) {a b : D}

/-- The common side of two distinct, non-monogon faces. These are local
incidence hypotheses, not any normalization or genus conclusion. -/
structure MergeSide (a b : D) : Prop where
  paired : M.edge a = b
  distinct_faces : ¬ M.face.SameCycle a b
  left_nonmonogon : M.face a ≠ a
  right_nonmonogon : M.face b ≠ b

namespace MergeSide
variable {M} (h : M.MergeSide a b)
include h
lemma ne : a ≠ b := fun he => M.edge_ne a (h.paired.trans he.symm)
lemma paired_back : M.edge b = a := by rw [← h.paired,M.edge_edge]
lemma face_left_ne_right : M.face a ≠ b := by
  intro he
  exact h.distinct_faces (he ▸ (SameCycle.rfl (x := a)).apply_right)
lemma face_right_ne_left : M.face b ≠ a := by
  intro he
  exact h.distinct_faces ((he ▸ (SameCycle.rfl (x := b)).apply_right).symm)
lemma edge_invariant (x : D) : OffPair a b (M.edge x) ↔ OffPair a b x := by
  change (M.edge x ≠ a ∧ M.edge x ≠ b) ↔ (x ≠ a ∧ x ≠ b)
  have h₁ : M.edge x = a ↔ x = b := by rw [← h.paired_back]; exact M.edge.apply_eq_iff_eq
  have h₂ : M.edge x = b ↔ x = a := by rw [← h.paired]; exact M.edge.apply_eq_iff_eq
  simp only [ne_eq,h₁,h₂,and_comm]

variable [DecidableEq D]

omit h in
lemma crossed_a : (M.face * swap a b) a = M.face b := by simp
lemma crossed_b : bypass (M.face * swap a b) a b = M.face a := by
  rw [bypass_away _ _ _ h.ne.symm]
  simp only [mul_apply,swap_apply_right,ite_eq_right h.left_nonmonogon]
omit [DecidableEq D] in
lemma vertex_a : M.vertex a = M.face b := by rw [vertex,mul_apply,h.paired]
lemma vertex_b : bypass M.vertex a b = M.face a := by
  rw [bypass_away _ _ _ h.ne.symm]
  have hb : M.vertex b = M.face a := by rw [vertex,mul_apply,h.paired_back]
  rw [hb,ite_eq_right h.left_nonmonogon]

/-- The exact permutation identity underlying deletion of a shared edge:
face cycles merge; the two endpoint vertex cycles only bypass the deleted
corners. Other contacts between the faces are immaterial. -/
lemma erase_identity :
    bypassPair (M.face * swap a b) a b * (swap a b * M.edge) =
      bypassPair M.vertex a b := by
  change swap b (bypass (M.face * swap a b) a b) *
    (swap a ((M.face * swap a b) a) * (M.face * swap a b)) * (swap a b * M.edge) =
    swap b (bypass M.vertex a b) * (swap a (M.vertex a) * M.vertex)
  rw [h.crossed_b,crossed_a,h.vertex_b,h.vertex_a]
  simp only [vertex,mul_assoc]
  rw [← mul_assoc (swap a b),swap_mul_self,one_mul]
end MergeSide

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_EdgeMergeComponents
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
variable {D : Type*} [DecidableEq D] [Fintype D]
namespace PictureMap
variable {M : PictureMap D} {a b : D} (h : M.MergeSide a b)
namespace MergeSide
include h

def representative (x : D) : {x // OffPair a b x} :=
  if hx : OffPair a b x then ⟨x,hx⟩ else
    ⟨M.face a,h.left_nonmonogon,h.face_left_ne_right⟩

omit [DecidableEq D] [Fintype D] in
lemma representative_kept (x : {x // OffPair a b x}) : h.representative x.val = x := by
  simp only [representative,dite_eq_left x.property]
omit [DecidableEq D] [Fintype D] in
lemma representative_a : h.representative a = ⟨M.face a,h.left_nonmonogon,h.face_left_ne_right⟩ := by
  simp [representative,OffPair]
omit [DecidableEq D] [Fintype D] in
lemma representative_b : h.representative b = ⟨M.face a,h.left_nonmonogon,h.face_left_ne_right⟩ := by
  simp [representative,OffPair]

end MergeSide

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StepChain
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
variable {D A : Type*} [DecidableEq D] [Fintype D] [AddCommMonoid A]

/-- Common-side cancellation and backtrack removal retain the EXACT sum of
oriented elementary cone triangles, with arbitrary additive coefficients. -/
lemma sum_offPair {a b : D} (hab : a ≠ b) (q : D → A) (hq : q a + q b = 0) :
    ∑ x : {x // OffPair a b x}, q x.val = ∑ x : D, q x := by
  have hs := Finset.sum_compl_add_sum ({a,b} : Finset D) q
  have hc : ∑ x ∈ ({a,b} : Finset D), q x = 0 := by simp [hab,hq]
  rw [hc,add_zero] at hs
  rw [← hs]
  symm
  exact Finset.sum_subtype _ (by intro x; simp [OffPair]) q

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkCancel
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

lemma free_of_opposite {a b : P.Dart} (ha : T.free (T.kind (P.index a)) = true)
    (hab : P.index b = T.opposite (P.index a)) : T.free (T.kind (P.index b)) = true := by
  rw [hab,T.opposite_kind]; exact ha

lemma reverse_label {a b : P.Dart} (hab : P.index b = T.opposite (P.index a)) :
    T.label (P.index a) = T.rev (T.label (P.index b)) := by
  rw [hab,T.opposite_label,T.rev_rev]

lemma mergeSide {a : P.Dart} (ha : T.free (T.kind (P.index a)) = true)
    (hop : P.index (P.pairing.edge a) = T.opposite (P.index a))
    (hf : ¬ P.pairing.face.SameCycle a (P.pairing.edge a)) :
    P.pairing.MergeSide a (P.pairing.edge a) :=
  ⟨rfl,hf,P.nonmonogon ha,P.nonmonogon (P.free_of_opposite ha hop)⟩

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkFanCapacity
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
open PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

lemma frozenCorner_start (g : FanTriangle n w) (o : Bool) :
    start n w (walkLabel n w d (frozenCorner n w d g o)) = .inr g.1 := by
  rw [frozenCorner_label]
  cases o <;> rfl

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkInstanceAt
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
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))
variable (select : P.Face → Bool)

def apexInstanceAt (b : Fan n w) (x : P.Dart)
    (hs : select (P.faceClass x) = true)
    (hx : start n w (walkLabel n w d (P.index x)) = .inr b) :
    ApexInstance n w d c hc f P select b :=
  ⟨P.vertexClass x,by
    have hh : P.pairing.vertex.SameCycle (P.vertexClass x).out x :=
      P.vertexClass_eq.mp (P.vertexClass_out _)
    exact (walk_start_link_constant n w d c hc f P hh).trans hx,
    x,rfl,hs⟩


end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualContact
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)

lemma rawDart_pair (x : P.Dart) : rawDart n w d c hc f P (P.pairing.edge x) ↔ rawDart n w d c hc f P x := by
  unfold rawDart
  have h : walkLabel n w d (P.index (P.pairing.edge x)) = rev n w (walkLabel n w d (P.index x)) := P.paired x
  rw [h]
  rfl

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkRadialBoundary
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
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))
variable (select : P.Face → Bool)

/-- Tags on actual apex corners are determined by their source dart. -/
lemma apexCorner_injective : Function.Injective
    (fun p : Σ b : Fan n w, Σ z : ApexInstance n w d c hc f P select b, P.Link z.val => p.2.2.val) := by
  rintro ⟨b,z,x⟩ ⟨a,y,k⟩ h
  have hb : b = a := Sum.inr.inj ((instance_start n w d c hc f P select b z x).symm.trans
    ((congrArg (fun t => start n w (walkLabel n w d (P.index t))) h).trans
      (instance_start n w d c hc f P select a y k)))
  subst a
  have hz : z = y := Subtype.ext (x.property.symm.trans ((congrArg P.vertexClass h).trans k.property))
  subst y
  exact Sigma.ext rfl (heq_of_eq (Sigma.ext rfl (heq_of_eq (Subtype.ext h))))

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Fragment
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
attribute [local instance] Classical.propDecidable
namespace HyperbolicObstruction
namespace IncidenceTemplate.Occurrences.Shape

lemma defectConstant_pos {α β δ : ℝ} (ha : 0 < α) (hb : 7*α < β) (hd : 0 < δ) :
    0 < defectConstant α β δ := by
  exact lt_min (sub_pos.mpr hb) (lt_min (div_pos ha (by norm_num)) hd)

end IncidenceTemplate.Occurrences.Shape
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PicturePartition
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.PictureMap.instFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r
variable {X I F : Type*} [Fintype X] [Fintype I] [Fintype F]

/-- Oriented side copies cut by a partition. Parallel contacts and self-contacts
remain literal side copies; no underlying-simple-graph collapse is made. -/
abbrev CutSide (P : PictureMap X) (part : X → I) := {x : X // part x ≠ part (P.edge x)}
instance instFintypeCutSide (P : PictureMap X) (part : X → I) : Fintype (CutSide P part) := Fintype.ofFinite _
abbrev CutContact (P : PictureMap X) (part : X → I) :=
  {x : X // part x ≠ part (P.edge x) ∧ P.number x < P.number (P.edge x)}
instance instFintypeCutContact (P : PictureMap X) (part : X → I) : Fintype (CutContact P part) := Fintype.ofFinite _

abbrev PartBoundary (P : PictureMap X) (part : X → I) (i : I) :=
  {x : X // part x = i ∧ part (P.edge x) ≠ i}
instance instFintypePartBoundary (P : PictureMap X) (part : X → I) (i : I) : Fintype (PartBoundary P part i) := Fintype.ofFinite _

lemma sum_part_boundary (P : PictureMap X) (part : X → I) :
    (∑ i, Fintype.card (PartBoundary P part i)) = Fintype.card (CutSide P part) := by
  rw [← Fintype.card_sigma]
  apply Fintype.card_congr
  exact {
    toFun := fun p => ⟨p.2.val,fun h => p.2.property.2 (h.symm.trans p.2.property.1)⟩
    invFun := fun x => ⟨part x.val,x.val,rfl,Ne.symm x.property⟩
    left_inv := by rintro ⟨i,x,hx,he⟩; cases hx; rfl
    right_inv := fun _ => rfl }

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualPartition
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
open Occurrences.Shape
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

variable {I : Type*} [Fintype I] (part : P.Face → I)

def partSelect (i : I) (F : P.Face) : Bool := decide (part F = i)

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeCellWalk
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- The actual oriented macro edge in the indexed attaching polygon. -/
def topDart (a : TopPolygon n w) (i : Fin a.2.2.val.length) : MacroGraph.graph.Dart :=
  ⟨(a.2.2.val.getVert i.val,
    a.2.2.val.getVert ((finRotate a.2.2.val.length) i).val),
    (MacroGraph.ofCycle a.2.2.val a.2.2.property).adjacent i⟩

/-- Forget only the choice of simple circuit surrounding a top step.
Frozen fan/decorative cell identities and all their positions are retained. -/
def cellWalkStep : (boundary n w d).Side → WalkStep n w d
  | ⟨.inl a,b,i⟩ => .inr ⟨.inl a,b,i⟩
  | ⟨.inr (.inl a),b,i⟩ => .inl (a.1,if b then topDart n w a i else (topDart n w a i).symm)
  | ⟨.inr (.inr a),b,i⟩ => .inr ⟨.inr a,b,i⟩

lemma cellWalkStep_label (s : (boundary n w d).Side) :
    walkLabel n w d (cellWalkStep n w d s) = (boundary n w d).sideLabel s := by
  rcases s with ⟨a,b,i⟩
  rcases a with a | (a | a)
  · rfl
  · cases b with
    | false => exact macroStep_reverse n w a.1 _
    | true => rfl
  · rfl

lemma cellWalkStep_kind (s : (boundary n w d).Side) :
    walkKind n w d (cellWalkStep n w d ((boundary n w d).next s)) =
      walkKind n w d (cellWalkStep n w d s) := by
  rcases s with ⟨a,b,i⟩
  rcases a with a | (a | a) <;> rfl

lemma cellWalkStep_frozen_next (s : (boundary n w d).Side)
    (h : walkFree n w d (walkKind n w d (cellWalkStep n w d s)) = false) :
    cellWalkStep n w d ((boundary n w d).next s) =
      (Equiv.sumCongr (1 : Perm (Top n w × MacroGraph.graph.Dart)) (frozenBoundary n w d).next)
        (cellWalkStep n w d s) := by
  rcases s with ⟨a,b,i⟩
  rcases a with a | (a | a)
  · rfl
  · cases h
  · rfl

lemma cellWalkStep_frozen_inj {s t : (boundary n w d).Side}
    (h : walkFree n w d (walkKind n w d (cellWalkStep n w d s)) = false)
    (he : cellWalkStep n w d s = cellWalkStep n w d t) : s = t := by
  rcases s with ⟨a,b,i⟩
  rcases t with ⟨a',b',i'⟩
  rcases a with a | (a | a)
  · rcases a' with a' | (a' | a')
    · have hh := Sum.inr.inj he
      have ha : a = a' := Sum.inl.inj (Sigma.mk.inj hh).1
      subst a'
      have hi := eq_of_heq (Sigma.mk.inj hh).2
      cases hi
      rfl
    · cases he
    · have hh := (Sigma.mk.inj (Sum.inr.inj he)).1
      cases hh
  · cases h
  · rcases a' with a' | (a' | a')
    · have hh := (Sigma.mk.inj (Sum.inr.inj he)).1
      cases hh
    · cases he
    · have hh := Sum.inr.inj he
      have ha : a = a' := Sum.inr.inj (Sigma.mk.inj hh).1
      subst a'
      have hi := eq_of_heq (Sigma.mk.inj hh).2
      cases hi
      rfl

universe u

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeDecorationGroup
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {H : Type*} [_root_.Group H] (c : Dart n w → H)
  (hc : ∀ e, c (rev n w e) = (c e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => c (side n w d a i))).prod = 1)

include hcell in
lemma six_relator_value (x : Fin 6 → Alphabet n) (present : d x = true) :
    (List.ofFn ((c ∘ letterDart n w) ∘ x)).prod = 1 := by
  exact hcell (.inr (.inr (.inr ⟨x,present⟩)))

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeFanGroup
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction
namespace ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {H : Type*} [_root_.Group H] (c : Dart n w → H)
  (hc : ∀ e, c (rev n w e) = (c e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => c (side n w d a i))).prod = 1)

def radialValue (b : Fan n w) (v : FanVertex b.val.1) : H := c (.inr ⟨b,v⟩,true)

include hc hcell in
lemma fanTriangle_relation (f : FanTriangle n w) :
    radialValue n w c f.1 (fanLeft n w f) * c (letterDart n w (fanLetter n w f)) =
      radialValue n w c f.1 (fanRight n w f) := by
  have he := hcell (.inl f)
  change c (.inr ⟨f.1,fanLeft n w f⟩,true) *
    (c (letterDart n w (fanLetter n w f)) *
      (c (.inr ⟨f.1,fanRight n w f⟩,false) * 1)) = 1 at he
  have hr := hc (.inr ⟨f.1,fanRight n w f⟩,true)
  change c (.inr ⟨f.1,fanRight n w f⟩,false) = _ at hr
  rw [hr,mul_one,← mul_assoc] at he
  exact mul_inv_eq_one.mp he

def fanPotential (b : Fan n w) : MasterGraph.Vertex → H
  | .inl v => if hv : IsFanVertex b.val.1 v then radialValue n w c b ⟨v,hv⟩ else 1
  | .inr _ => 1

include hc hcell in
lemma fanPotential_edge (b : Fan n w) (e : IncidenceTemplate.Edge) (he : e ∈ fan b.val.1) :
    fanPotential n w c b (MasterGraph.source (.inl e)) *
      c (letterDart n w (b.val.2 ⟨.inl e,by simpa [rowSupport] using he⟩)) =
    fanPotential n w c b (MasterGraph.target (.inl e)) := by
  have hf := fanTriangle_relation n w d c hc hcell ⟨b,⟨e,he⟩⟩
  simpa only [fanPotential,MasterGraph.source,MasterGraph.target,
    dite_eq_left (edge_fan_vertices e b.val.1 he).1,
    dite_eq_left (edge_fan_vertices e b.val.1 he).2,
    fanLetter,fanLeft,fanRight] using hf

end ConeSkeleton
end HyperbolicObstruction
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeTopGroup
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {H : Type*} [_root_.Group H] (c : Dart n w → H)
  (hc : ∀ e, c (rev n w e) = (c e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => c (side n w d a i))).prod = 1)

lemma row_extendCore_fan (l : Field → Alphabet n) (i : Fin 7) :
    TableModel.row rowSupport (extendCore n (fun e => l (.inl e))) (.inl i) =
    TableModel.row rowSupport l (.inl i) := by
  unfold TableModel.row
  apply congrArg (Sigma.mk _)
  funext f
  rcases f with ⟨e | s,h⟩
  · rfl
  · simp [rowSupport] at h

lemma row_extendCore_top (l : Field → Alphabet n) :
    TableModel.row rowSupport (extendCore n (fun e => l (.inl e))) (.inr (.inl ())) =
    TableModel.row rowSupport l (.inr (.inl ())) := by
  unfold TableModel.row
  apply congrArg (Sigma.mk _)
  funext f
  rcases f with ⟨e | s,h⟩
  · rfl
  · simp [rowSupport] at h

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonSphereFurther
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary
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
variable {D B : Type*}

namespace PolygonSphere
variable {I : Type*} (q : Perm I)

/-- The sphere obtained by pairing a polygon with a reversed copy. It is the
literal base case of a cellular disk picture after adjoining its outside. -/
def pairing : PictureMap (Bool × I) where
  face := turn q
  edge := flip
  edge_sq := by apply Equiv.ext; rintro ⟨b,i⟩; cases b <;> rfl
  edge_ne := by rintro ⟨b,i⟩ he; cases b <;> exact Bool.noConfusion (congrArg Prod.fst he)

lemma face_sameCycle_pos {i j : I} (h : q.SameCycle i j) :
    (turn q).SameCycle (true,i) (true,j) :=
  semiconj_perm_sameCycle (j := fun i => (true,i)) (fun _ => rfl) h

lemma face_sameCycle_neg {i j : I} (h : q.SameCycle i j) :
    (turn q).SameCycle (false,i) (false,j) :=
  semiconj_perm_sameCycle (j := fun i => (false,i)) (fun _ => rfl) h.inv

lemma face_classes (hq : ∀ i j, q.SameCycle i j) (x y : Bool × I) :
    (turn q).SameCycle x y ↔ x.1 = y.1 := by
  constructor
  · intro h
    exact sameCycle_one.mp (semiconj_perm_sameCycle (t := (1 : Perm Bool))
      (j := Prod.fst) (turn_orientation q) h)
  · rcases x with ⟨b,i⟩; rcases y with ⟨c,j⟩
    intro h
    cases h
    cases b
    · exact face_sameCycle_neg q (hq i j)
    · exact face_sameCycle_pos q (hq i j)

lemma vertex_index (x : Bool × I) : vertexIndex q ((pairing q).vertex x) = vertexIndex q x := by
  rcases x with ⟨b,i⟩; cases b <;> simp [vertexIndex,PictureMap.vertex,pairing,turn,flip]

lemma vertex_classes (x y : Bool × I) :
    (pairing q).vertex.SameCycle x y ↔ vertexIndex q x = vertexIndex q y := by
  constructor
  · intro h
    exact sameCycle_one.mp (semiconj_perm_sameCycle (t := (1 : Perm I))
      (j := vertexIndex q) (vertex_index q) h)
  · rcases x with ⟨b,i⟩; rcases y with ⟨c,j⟩
    cases b <;> cases c <;> intro h
    · have he : i = j := q.injective h
      subst j
      exact SameCycle.rfl
    · have he : q i = j := h
      subst j
      exact SameCycle.rfl.apply_right
    · have he : i = q j := h
      subst i
      have h' : (pairing q).vertex (true,q j) = (false,j) := by
        simp [PictureMap.vertex,pairing,turn,flip]
      exact h' ▸ (SameCycle.rfl (x := (true,q j))).apply_right
    · have he : i = j := h
      subst j
      exact SameCycle.rfl

end PolygonSphere
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureMirror
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary
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
variable {D : Type*} [DecidableEq D] [Fintype D]

lemma cycles_inverse (p : Perm D) : cycles p⁻¹ = cycles p := by
  simp only [cycles,defect,support_inv,cycleType_inv]

lemma cycles_conjugate (p q : Perm D) : cycles (q*p*q⁻¹) = cycles p := by
  simp only [cycles,defect,card_support_conj,cycleType_conj]

namespace PictureMap
variable (M : PictureMap D)

/-- Reflection reverses every face orientation; side pairs are unchanged. -/
def mirror : PictureMap D where
  face := M.face⁻¹
  edge := M.edge
  edge_sq := M.edge_sq
  edge_ne := M.edge_ne

lemma mirror_euler : M.mirror.euler = M.euler := by
  have hi : M.edge⁻¹ = M.edge := by
    apply inv_eq_of_mul_eq_one_left
    exact M.edge_sq
  have hv : M.mirror.vertex = M.edge * M.vertex⁻¹ * M.edge⁻¹ := by
    simp only [vertex,mirror,mul_inv_rev,hi,mul_assoc]
    rw [← mul_assoc M.edge M.edge,M.edge_sq,one_mul]
  rw [euler,euler,hv,cycles_conjugate,cycles_inverse]
  change cycles M.vertex + cycles M.face⁻¹ - _ = _
  rw [cycles_inverse]

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordPicture
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.WordPictures
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable {A : Type u}

attribute [instance] WordPicture.finite WordPicture.decEq

namespace WordPicture
variable {R : Set (Word A)} {w : Word A} (P : WordPicture R w)

/-- No faces are required to fill the empty word. -/
def empty (R : Set (Word A)) : WordPicture R [] where
  Dart := PEmpty
  pairing := {
    face := 1
    edge := 1
    edge_sq := one_mul _
    edge_ne := fun x => PEmpty.elim x }
  genusZero := by
    simp only [PictureMap.GenusZero,PictureMap.euler,PictureMap.vertex,
      cycles,defect,Fintype.card_pempty,one_mul,support_one,Finset.card_empty,
      cycleType_one,Multiset.card_zero,Nat.cast_zero,sub_zero,add_zero,Int.zero_ediv,
      zero_eq_mul]
    right
    norm_cast
    apply Nat.card_eq_zero.mpr
    exact Or.inl ⟨fun x => Quotient.inductionOn x (fun x => PEmpty.elim x)⟩
  label := PEmpty.elim
  paired := fun x => PEmpty.elim x
  outside := []
  boundary := ⟨by simp,fun _ h => False.elim (List.not_mem_nil h)⟩
  word := rfl
  interior := fun x => PEmpty.elim x

end WordPicture
end HyperbolicObstruction.WordPictures
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TreeCentroid
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open Finset
variable {V : Type*} [Fintype V]

/-- A finite weighted tree has a centroid: each branch at the selected vertex
has at most half the total weight. This is a genuine weighted-tree theorem,
not a planar-separator assumption. -/
theorem weighted_tree_centroid (G : SimpleGraph V) (hG : G.IsTree) (weight : V → ℝ) :
    ∃ v : V, ∀ w : V, G.Adj v w →
      2 * ∑ x ∈ treeBranch G v w, weight x ≤ ∑ x : V, weight x := by
  let potential : V → ℝ := fun v => ∑ x : V, weight x * G.dist x v
  have : Nonempty V := hG.connected.nonempty
  obtain ⟨v, _, hmin⟩ := Finset.exists_min_image Finset.univ potential Finset.univ_nonempty
  refine ⟨v,?_⟩
  intro w hadj
  have hid : potential w + 2 * ∑ x ∈ treeBranch G v w, weight x =
      potential v + ∑ x : V, weight x := by
    unfold potential treeBranch
    rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rcases hG.dist_eq_dist_add_one_of_adj x hadj with h | h
    · have hx : G.dist x w < G.dist x v := by omega
      rw [ite_eq_left hx,h,Nat.cast_add,Nat.cast_one]
      ring
    · have hx : ¬G.dist x w < G.dist x v := by omega
      rw [ite_eq_right hx,h,Nat.cast_add,Nat.cast_one]
      ring
  have hle := hmin w (Finset.mem_univ w)
  linarith

end HyperbolicObstruction.PlanarRecursion
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TreeCentroidCut
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open Finset SimpleGraph
variable {V : Type*}

variable [Fintype V] [DecidableEq V]

/-- The weighted centroid really separates the tree: every connected set
remaining after removing it has at most half the total weight. All weights
are on actual vertices and no combinatorial separation is hypothesized. -/
theorem weighted_tree_vertex_separator (G : SimpleGraph V) (hG : G.IsTree)
    (weight : V → ℝ) (hw : ∀ x, 0 ≤ weight x) :
    ∃ v : V, ∀ S : Finset V, v ∉ S → (G.induce (S : Set V)).Preconnected →
      2 * ∑ x ∈ S, weight x ≤ ∑ x : V, weight x := by
  obtain ⟨v,hv⟩ := weighted_tree_centroid G hG weight
  refine ⟨v,?_⟩
  intro S hvS hconn
  by_cases hS : S.Nonempty
  · obtain ⟨x,hx⟩ := hS
    obtain ⟨p,hp,_⟩ := hG.connected.exists_path_of_dist v x
    cases p with
    | nil => exact (hvS hx).elim
    | @cons v w x hadj q =>
      have havoid : v ∉ q.support := by
        have hnodup := hp.support_nodup
        exact (List.nodup_cons.mp (by simpa only [Walk.support_cons] using hnodup)).1
      have hsub : S ⊆ treeBranch G v w := by
        intro y hy
        obtain ⟨r⟩ := hconn ⟨y,hy⟩ ⟨x,hx⟩
        let r' := r.map (SimpleGraph.Embedding.induce (S : Set V)).toHom
        have hr' : v ∉ r'.support := by
          intro h
          rw [Walk.support_map] at h
          obtain ⟨z,_,hz⟩ := List.mem_map.mp h
          exact hvS (hz ▸ z.property)
        apply treeBranch_of_avoiding_walk hG hadj (r'.append q.reverse)
        intro h
        have hh := (Walk.mem_support_append_iff r' q.reverse).mp h
        rcases hh with hh | hh
        · exact hr' hh
        · exact havoid (by simpa using hh)
      exact le_trans (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hw x)) (by norm_num)) (hv w hadj)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp only [Finset.sum_empty,mul_zero]
    exact Finset.sum_nonneg (fun x _ => hw x)

end HyperbolicObstruction.PlanarRecursion
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TreeCentroidComponents
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
attribute [local instance] Classical.propDecidable
open SimpleGraph
variable {V : Type*}

variable [Fintype V] [DecidableEq V]

/-- Actual components after deleting a weighted tree centroid carry at most
half the total mass. The isolated centroid component is explicitly excluded. -/
theorem weighted_tree_component_separator (G : SimpleGraph V) (hG : G.IsTree)
    (weight : V → ℝ) (hw : ∀ x, 0 ≤ weight x) :
    ∃ v : V, ∀ C : (G.deleteIncidenceSet v).ConnectedComponent,
      C ≠ (G.deleteIncidenceSet v).connectedComponentMk v →
      2 * ∑ x ∈ C.supp.toFinset, weight x ≤ ∑ x : V, weight x := by
  classical
  obtain ⟨v,hv⟩ := weighted_tree_vertex_separator G hG weight hw
  refine ⟨v,?_⟩
  intro C hC
  have hnot : v ∉ C.supp := fun h => hC h.symm
  apply hv C.supp.toFinset
  · simpa only [Set.mem_toFinset] using hnot
  · have hc := C.connected_toSimpleGraph.preconnected
    change ((G.deleteIncidenceSet v).induce C.supp).Preconnected at hc
    rw [G.induce_deleteIncidenceSet_of_notMem hnot] at hc
    have he : (C.supp.toFinset : Set V) = C.supp := Set.coe_toFinset C.supp
    rw [he]
    exact hc

end HyperbolicObstruction.PlanarRecursion
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SeparatorGrouping
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Convert the connected-remainder formulation into the literal three
regions required by the recursive partition theorem. -/
theorem label_of_component_separator (G : SimpleGraph V) (U S : Finset V)
    (hSU : S ⊆ U)
    (hsep : ∀ W : Finset V, W ⊆ U → Disjoint W S →
      (G.induce (W : Set V)).Preconnected → 2*W.card ≤ U.card) :
    ∃ t : V → Fin 3, region U t 0 = S ∧
      3*(region U t 1).card ≤ 2*U.card ∧
      3*(region U t 2).card ≤ 2*U.card ∧
      ∀ x ∈ region U t 1, ∀ y ∈ region U t 2, ¬G.Adj x y := by
  classical
  let R := U \ S
  let H := G.induce (R : Set V)
  let : Fintype H.ConnectedComponent := Fintype.ofFinite _
  let color : V → Option H.ConnectedComponent := fun v =>
    if hv : v ∈ R then some (H.connectedComponentMk ⟨v,hv⟩) else none
  have hcolor (v : V) (hv : v ∈ R) : color v = some (H.connectedComponentMk ⟨v,hv⟩) :=
    dite_eq_left hv
  let fiber := fun i => R.filter (fun v => color v = i)
  have htotal : ∑ i, (fiber i).card ≤ U.card := by
    have he := Finset.sum_card_fiberwise_eq_card_filter R
      (Finset.univ : Finset (Option H.ConnectedComponent)) color
    simp only [Finset.mem_univ,Finset.filter_true] at he
    exact he.le.trans (Finset.card_le_card Finset.sdiff_subset)
  have hblock : ∀ i, 2*(fiber i).card ≤ U.card := by
    intro i
    have hsub : fiber i ⊆ U := (Finset.filter_subset _ _).trans Finset.sdiff_subset
    have hdisj : Disjoint (fiber i) S := by
      apply Finset.disjoint_left.mpr
      intro v hv hvs
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).2 hvs
    cases i with
    | none =>
      have he : fiber none = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        have hvR := (Finset.mem_filter.mp hv).1
        have hn := (Finset.mem_filter.mp hv).2
        rw [hcolor v hvR] at hn
        cases hn
      simp [he]
    | some c =>
      apply hsep _ hsub hdisj
      let g : c.toSimpleGraph →g G.induce (fiber (some c) : Set V) := {
        toFun := fun v => ⟨v.val.val,Finset.mem_filter.mpr ⟨v.val.property,by
          rw [hcolor _ v.val.property]
          exact congrArg some v.property⟩⟩
        map_rel' := fun h => h }
      apply c.connected_toSimpleGraph.preconnected.map g
      intro v
      have hvR := (Finset.mem_filter.mp v.property).1
      have hvC := (Finset.mem_filter.mp v.property).2
      rw [hcolor v.val hvR] at hvC
      exact ⟨⟨⟨v.val,hvR⟩,Option.some.inj hvC⟩,Subtype.ext rfl⟩
  obtain ⟨A,hA,hAc⟩ := balanced_grouping (fun i => (fiber i).card) U.card htotal hblock
  let t : V → Fin 3 := fun v => if v ∈ S then 0 else if color v ∈ A then 1 else 2
  have hzero : region U t 0 = S := by
    ext v
    simp only [mem_region,t]
    by_cases hs : v ∈ S
    · simp [hs,hSU hs]
    · by_cases hc : color v ∈ A <;> simp [hs,hc]
  have hone : region U t 1 = R.filter (fun v => color v ∈ A) := by
    ext v
    simp only [mem_region,Finset.mem_filter,Finset.mem_sdiff,t,R]
    by_cases hs : v ∈ S <;> by_cases hc : color v ∈ A <;> simp [hs,hc]
  have htwo : region U t 2 = R.filter (fun v => color v ∈ Aᶜ) := by
    ext v
    simp only [mem_region,Finset.mem_filter,Finset.mem_sdiff,t,R,Finset.mem_compl]
    by_cases hs : v ∈ S <;> by_cases hc : color v ∈ A <;> simp [hs,hc]
  have hcardA := Finset.sum_card_fiberwise_eq_card_filter R A color
  have hcardAc := Finset.sum_card_fiberwise_eq_card_filter R Aᶜ color
  refine ⟨t,hzero,?_,?_,?_⟩
  · rw [hone,← hcardA]
    exact hA
  · rw [htwo,← hcardAc]
    exact hAc
  · intro x hx y hy hadj
    rw [hone] at hx
    rw [htwo] at hy
    obtain ⟨hxR,hxA⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyR,hyA⟩ := Finset.mem_filter.mp hy
    have he : color x = color y := by
      rw [hcolor x hxR,hcolor y hyR]
      exact congrArg some (ConnectedComponent.sound (show H.Reachable ⟨x,hxR⟩ ⟨y,hyR⟩ from
        (show H.Adj ⟨x,hxR⟩ ⟨y,hyR⟩ from hadj).reachable))
    rw [← he] at hyA
    exact Finset.mem_compl.mp hyA hxA

/-- A uniform sqrt component-separator theorem supplies the exact recursive
separator interface, with no factor depending on the carrier or graph. -/
theorem balanced_separators_of_component_separators (G : SimpleGraph V) (c : ℕ)
    (h : ∀ U : Finset V, ∃ S : Finset V, S ⊆ U ∧ S.card ≤ c*Nat.sqrt U.card ∧
      ∀ W : Finset V, W ⊆ U → Disjoint W S →
        (G.induce (W : Set V)).Preconnected → 2*W.card ≤ U.card) :
    HasBalancedSeparators G c := by
  intro U
  obtain ⟨S,hSU,hSc,hsep⟩ := h U
  obtain ⟨t,ht,h1,h2,hno⟩ := label_of_component_separator G U S hSU hsep
  refine ⟨t,?_,h1,h2,hno⟩
  rw [ht]
  have hroot : (Nat.sqrt U.card : ℝ) ≤ Real.sqrt U.card := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    have hh := Nat.sqrt_le U.card
    norm_cast
    simpa only [pow_two] using hh
  have hh : (S.card : ℝ) ≤ (c : ℝ)*(Nat.sqrt U.card : ℝ) := by exact_mod_cast hSc
  exact hh.trans (mul_le_mul_of_nonneg_left hroot (by positivity))

end HyperbolicObstruction.PlanarRecursion
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkCover
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary
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
universe u v w z k t r q p
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]

/-- Literal voltage data for a regular cover of the indexed cell target.
`offset` is the position of a side's initial vertex relative to its cell lift.
These are local edge equations, not a chain-vanishing assumption. -/
structure WalkCellCover (T : WalkCellTarget S C W L V A) (G : Type q) [Group G] where
  voltage : L → G
  voltage_rev : ∀ l, voltage (T.rev l) = (voltage l)⁻¹
  offset : S → G
  offset_opposite : ∀ s, offset (T.opposite s) = offset s * voltage (T.label s)
  free_back : ∀ s t, T.free (T.kind s) = true → T.kind s = T.kind t →
    T.back s = T.back t → offset (T.opposite s) = offset (T.opposite t)

namespace WalkCellCover
variable {T : WalkCellTarget S C W L V A} {G : Type q} [Group G]
  (H : WalkCellCover T G) {B : Type p} [AddCommMonoid B]

lemma offset_opposite_opposite (s : S) : H.offset (T.opposite (T.opposite s)) = H.offset s := by
  rw [H.offset_opposite,H.offset_opposite,T.opposite_label,H.voltage_rev,mul_inv_cancel_right]

def target (weight : G → S → B)
    (hw : ∀ g s, T.free (T.kind s) = true → weight g s + weight g (T.opposite s) = 0) :
    WalkCellTarget (G × S) (G × C) (G × W) (G × L) (G × V) B where
  kind s := (s.1,T.kind s.2)
  free c := T.free c.2
  front s := (s.1 * H.offset s.2,T.front s.2)
  back s := (s.1 * H.offset (T.opposite s.2),T.back s.2)
  vertex x := (x.1,T.vertex x.2)
  label s := (s.1 * H.offset s.2,T.label s.2)
  start l := (l.1,T.start l.2)
  rev l := (l.1 * H.voltage l.2,T.rev l.2)
  rev_rev := by intro l; ext <;> simp [T.rev_rev,H.voltage_rev]
  front_label := by intro s; exact Prod.ext rfl (T.front_label s.2)
  back_label := by
    intro s; apply Prod.ext
    · exact (mul_assoc _ _ _).trans (congrArg (s.1 * ·) (H.offset_opposite s.2).symm)
    · exact T.back_label s.2
  opposite s := (s.1,T.opposite s.2)
  opposite_kind := by intro s; exact Prod.ext rfl (T.opposite_kind s.2)
  opposite_front := by intro s; exact Prod.ext rfl (T.opposite_front s.2)
  opposite_back := by
    intro s; exact Prod.ext (congrArg (s.1 * ·) (H.offset_opposite_opposite s.2)) (T.opposite_back s.2)
  opposite_label := by
    intro s; apply Prod.ext
    · exact (congrArg (s.1 * ·) (H.offset_opposite s.2)).trans (mul_assoc _ _ _).symm
    · exact T.opposite_label s.2
  loopless := by intro s hs he; exact T.loopless s.2 hs (congrArg Prod.snd he)
  simple := by
    intro s t hs hk hf hb
    exact Prod.ext (congrArg (fun q : G × C => q.1) hk)
      (T.simple s.2 t.2 hs (congrArg Prod.snd hk) (congrArg Prod.snd hf) (congrArg Prod.snd hb))
  weight s := weight s.1 s.2
  opposite_weight := by intro s hs; exact hw s.1 s.2 hs

variable (weight : G → S → B)
  (hw : ∀ g s, T.free (T.kind s) = true → weight g s + weight g (T.opposite s) = 0)

def frozenTarget (F : FrozenTarget T)
    (hw' : ∀ g s, weight g s + weight g (T.opposite s) = 0) :
    FrozenTarget (H.target weight hw) where
  next := Equiv.prodCongr (Equiv.refl G) F.next
  reverse := Equiv.prodCongr (Equiv.refl G) F.reverse
  reverse_eq := by intro s; exact Prod.ext rfl (F.reverse_eq s.2)
  reverse_sq := by
    apply Equiv.ext; intro s
    change (s.1,F.reverse (F.reverse s.2)) = (s.1,s.2)
    apply Prod.ext
    · rfl
    · exact Equiv.congr_fun F.reverse_sq s.2
  reverse_next := by intro s; exact Prod.ext rfl (F.reverse_next s.2)
  opposite_cycle := by
    intro s hh
    apply F.opposite_cycle s.2
    exact semiconj_perm_sameCycle (j := (Prod.snd : G × S → S)) (fun _ => rfl) hh
  opposite_weight := by
    intro s
    change weight s.1 s.2 + weight s.1 (F.reverse s.2) = 0
    rw [F.reverse_eq]; exact hw' s.1 s.2

variable (P : WalkPicture.{u} (H.target weight hw))

/-- Forget deck coordinates but not a single dart or face. -/
def forget : WalkPicture.{u} T where
  Dart := P.Dart
  pairing := P.pairing
  index x := (P.index x).2
  closed := by intro x; exact congrArg Prod.snd (P.closed x)
  kind := by intro x; exact congrArg Prod.snd (P.kind x)
  paired := by intro x; exact congrArg Prod.snd (P.paired x)
  genusZero := P.genusZero

lemma deck_face {a b : P.Dart} (hab : P.pairing.face.SameCycle a b) :
    (P.index a).1 = (P.index b).1 :=
  congrArg (fun q : G × C => q.1) (PictureMap.kind_cycle P.kind hab)

lemma forget_fullyReduced (hs : P.FullyReduced) : (H.forget weight hw P).FullyReduced := by
  intro a he
  apply hs a
  apply Prod.ext
  · have hp := congrArg Prod.fst (P.paired a)
    change (P.index (P.pairing.edge a)).1 * H.offset (P.index (P.pairing.edge a)).2 =
      ((P.index a).1 * H.offset (P.index a).2) * H.voltage (T.label (P.index a).2) at hp
    change (P.index (P.pairing.edge a)).2 = T.opposite (P.index a).2 at he
    rw [he,H.offset_opposite,mul_assoc] at hp
    exact mul_right_cancel hp
  · exact he

lemma forget_radialInjective (apex : V → Bool)
    (hs : P.RadialInjective (apex ∘ Prod.snd)) :
    (H.forget weight hw P).RadialInjective apex := by
  intro a b ha hab he
  apply hs a b ha hab
  apply Prod.ext
  · have hv := sameCycle_le_of_apply
      (s := Setoid.ker (fun x : P.Dart => (H.target weight hw).start ((H.target weight hw).label (P.index x))))
      (fun x => (P.respects.1 x).symm) hab
    exact congrArg (fun q : G × V => q.1) hv
  · exact he

lemma forget_frozenMapped (F : FrozenTarget T)
    (hw' : ∀ g s, weight g s + weight g (T.opposite s) = 0)
    (hm : P.FrozenMapped (H.frozenTarget weight hw F hw')) :
    (H.forget weight hw P).FrozenMapped F := by
  constructor
  · intro x; exact congrArg Prod.snd (hm.commute x)
  · intro x y hxy he
    apply hm.injective hxy
    apply Prod.ext
    · exact H.deck_face weight hw P (semiconj_perm_sameCycle (j := (Subtype.val : P.FrozenDart → P.Dart)) (fun _ => rfl) hxy)
    · exact he

end WalkCellCover
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LiftedClosedPicture
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable
universe u v z

/-- Zero coefficients specify the base indexing target only: the cover
has arbitrary independent weights for each lifted step. -/
def indexingTarget (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
    (d : (Fin 6 → Alphabet n) → Bool) :=
  walkTarget n w d (fun _ _ => (0 : ℤ)) (by simp) (fun _ => 0)

def indexingFrozenTarget (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
    (d : (Fin 6 → Alphabet n) → Bool) :=
  walkFrozenTarget n w d (fun _ _ => (0 : ℤ)) (by simp) (fun _ => 0)

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeCover
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)

/-- Cell lift coordinate at a frozen side, measured from its indexed first
vertex. Reversing orientation changes the initial point but not the cell lift. -/
def frozenOffset (s : (frozenBoundary n w d).Side) : G :=
  let p := (((List.ofFn ((frozenBoundary n w d).label s.1)).take s.2.2.val).map v).prod
  if s.2.1 then p else p * v ((frozenBoundary n w d).label s.1 s.2.2)

include hv in
lemma frozenOffset_opposite (s : (frozenBoundary n w d).Side) :
    frozenOffset n w d v ((frozenBoundary n w d).opposite s) =
      frozenOffset n w d v s * v ((frozenBoundary n w d).sideLabel s) := by
  rcases s with ⟨a,b,i⟩
  cases b with
  | false =>
    change _ = (_ * v ((frozenBoundary n w d).label a i)) * v (rev n w ((frozenBoundary n w d).label a i))
    rw [hv,mul_inv_cancel_right]
    rfl
  | true => rfl

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_CoreWordGraph
attribute [-instance] _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.CoreWordGraph
open IncidenceTemplate CoreGeometry MasterGraph LetterPresentation SimpleGraph
variable (S : Finset IncidenceTemplate.Edge)

def projection : MasterGraph.Vertex → CoreGeometry.Vertex
  | .inl x => x
  | .inr _ => .inl 0

end HyperbolicObstruction.CoreWordGraph
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_EdgeContraction
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! In a genuinely simply connected space, individual graph edges contract
with arbitrary prescribed vertex tracks. -/
noncomputable section
open scoped Topology unitInterval
namespace HyperbolicObstruction.EdgeContraction
variable {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]
  {a b z : X} (p : Path a b) (pa : Path a z) (pb : Path b z)

def square : C(I × I,X) := SquarePathFilling.fill
  (SimplyConnectedSpace.paths_homotopic (p.trans pb) (pa.trans (Path.refl z))).some

def contraction : C(I × I,X) := (square p pa pb).comp ⟨Prod.swap,continuous_swap⟩
@[simp] lemma contraction_initial (s : I) : contraction p pa pb (0,s) = p s :=
  SquarePathFilling.fill_bottom _ s
@[simp] lemma contraction_final (s : I) : contraction p pa pb (1,s) = z :=
  SquarePathFilling.fill_top _ s
@[simp] lemma contraction_left (t : I) : contraction p pa pb (t,0) = pa t :=
  SquarePathFilling.fill_left _ t
@[simp] lemma contraction_right (t : I) : contraction p pa pb (t,1) = pb t :=
  SquarePathFilling.fill_right _ t

end HyperbolicObstruction.EdgeContraction
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FinitePolyhedron
attribute [-instance] _root_.OAI.HyperbolicObstruction.FinitePolyhedron.openStar_contractible _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! Literal barycentric realizations of finite abstract complexes. No abstract
CW or homotopy replacement is used in the definitions. -/
noncomputable section
open scoped Topology
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [Fintype V]

lemma simplex_closed (s : Finset V) : IsClosed (simplex s) := by
  change IsClosed ({point : V → ℝ | ∀ index, 0 ≤ point index} ∩
    ({point : V → ℝ | (∑ index, point index) = 1} ∩
      {point : V → ℝ | ∀ index, index ∉ s → point index = 0}))
  apply IsClosed.inter
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun index =>
      isClosed_le continuous_const (continuous_apply index)
  · apply IsClosed.inter
    · exact isClosed_eq (by fun_prop) continuous_const
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun index => isClosed_iInter fun _ =>
        isClosed_eq (continuous_apply index) continuous_const

lemma simplex_compact (s : Finset V) : IsCompact (simplex s) := by
  refine (isCompact_Icc : IsCompact (Set.Icc (0 : V → ℝ) 1)).of_isClosed_subset
    (simplex_closed s) ?_
  intro point hpoint
  refine ⟨hpoint.1, fun index => ?_⟩
  calc
    point index ≤ ∑ other, point other :=
      Finset.single_le_sum (fun other _ => hpoint.1 other) (Finset.mem_univ index)
    _ = 1 := hpoint.2.1

lemma carrierSet_eq_union (K : AbstractSimplicialComplex V) :
    carrierSet K = ⋃ s ∈ K.faces, simplex s := by
  ext x
  simp only [carrierSet, Set.mem_ofPred_eq, Set.mem_iUnion, simplex]
  exact ⟨fun ⟨h0,h1,s,hs,hx⟩ => ⟨s,hs,h0,h1,hx⟩,
    fun ⟨s,hs,h0,h1,hx⟩ => ⟨h0,h1,s,hs,hx⟩⟩

lemma carrierSet_compact (K : AbstractSimplicialComplex V) : IsCompact (carrierSet K) := by
  rw [carrierSet_eq_union]
  exact Set.toFinite K.faces |>.isCompact_biUnion (fun s _ => simplex_compact s)

instance instCompactSpaceElemForallRealCarrier (K : AbstractSimplicialComplex V) : CompactSpace (Carrier K) :=
  isCompact_iff_compactSpace.mp (carrierSet_compact K)

end HyperbolicObstruction.FinitePolyhedron
end
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

lemma next_ne (q : P.Position) : P.next q ≠ q := by
  rcases q with ⟨c,i,j⟩
  intro h
  have hh := congrArg (fun a : P.Position => a.2.2.val) h
  simp only [Data.next] at hh
  split_ifs at hh with hj
  · change (0 : ℕ) = j.val at hh
    omega
  · change j.val + 1 = j.val at hh
    omega

variable [DecidableEq V] [DecidableEq E] [DecidableEq C]

lemma facet_face (f : P.Facet) : P.facet f ∈ P.complex.faces := by
  refine ⟨?_,Or.inr ⟨f,Finset.Subset.refl _⟩⟩
  cases f with
  | inl e => dsimp [facet,graphFace]; split_ifs <;> simp
  | inr q => dsimp [facet,collarFace]; split_ifs <;> simp

end Data
end HyperbolicObstruction.FinitePolygonModel
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FinitePolyhedronVoltage
attribute [-instance] _root_.OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.deckAction _root_.OAI.HyperbolicObstruction.FinitePolyhedron.openStar_contractible _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal flat principal covering of a barycentric polyhedron, obtained
from edge voltages satisfying exactly the two-dimensional face relations.
The topology is Mathlib's fiber-bundle gluing topology, not the product.
This construction does not assert that the cover is simply connected. -/
noncomputable section

open scoped Topology
open Set
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [Fintype V] (K : AbstractSimplicialComplex V)

variable [DecidableEq V]

variable (G : Type*) [Group G]

namespace Voltage
variable {K G} (v : Voltage K G)

variable [TopologicalSpace G] [DiscreteTopology G]

lemma isCoveringMap : IsCoveringMap v.proj := FiberBundle.isCoveringMap

lemma proj_surjective : Function.Surjective v.proj := fun x => ⟨⟨x,(1 : G)⟩,rfl⟩

end Voltage
end HyperbolicObstruction.FinitePolyhedron
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IntegralCellularBoundary
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-!
Integral chains for a polygon incidence system, with all lifted edges independent.
This is the algebraic cellular boundary needed for the source's cycle producer.
It does not identify these chains with a topological homology theory.
-/
noncomputable section
namespace HyperbolicObstruction
namespace IntegralIncidence

variable {E V G C : Type*} [Group G]

variable (start : E × Bool → V) (voltage : E × Bool → G)

variable (hv : ∀ e, voltage (reverse e) = (voltage e)⁻¹)

lemma group_prefix_rotate {G : Type*} [Group G] {m : ℕ} (p : Fin m → G)
    (hp : (List.ofFn p).prod = 1) (i : Fin m) :
    ((List.ofFn p).take ((finRotate m i).val)).prod =
      ((List.ofFn p).take i.val).prod * p i := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ m =>
    have hs := List.prod_take_succ (List.ofFn p) i.val (by simpa only [List.length_ofFn] using i.isLt)
    have he : (List.ofFn p)[i.val] = p i := List.getElem_ofFn (by simpa only [List.length_ofFn] using i.isLt)
    rw [he] at hs
    by_cases hi : i = Fin.last m
    · subst i
      rw [finRotate_apply,Fin.val_add_one,ite_eq_left rfl]
      have hlen : (Fin.last m).val + 1 = (List.ofFn p).length := by simp only [Fin.val_last,List.length_ofFn]
      rw [hlen,List.take_length,hp] at hs
      simpa only [List.take_zero,List.prod_nil] using hs
    · rw [finRotate_apply,Fin.val_add_one,ite_eq_right hi]
      exact hs


end IntegralIncidence
end HyperbolicObstruction
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FinitePolygonVoltage
attribute [-instance] _root_.OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.deckAction _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal source voltages on the mapping-cylinder triangulation. -/
noncomputable section

namespace HyperbolicObstruction.FinitePolygonModel.Data
open FinitePolyhedron
variable {V E C G : Type*} [Group G]
variable (P : Data V E C) (v : E → G)

def segment (q : P.Position) : G := if q.2.2.val = 1 then signed v (P.side q.1 q.2.1) else 1

def cornerOffset (q : P.Position) : G :=
  ((List.ofFn (fun i => signed v (P.side q.1 i))).take q.2.1.val).prod *
    (if q.2.2.val = 2 then signed v (P.side q.1 q.2.1) else 1)

lemma cornerOffset_next (h : ∀ c, (List.ofFn (fun i => signed v (P.side c i))).prod = 1)
    (q : P.Position) : P.cornerOffset v (P.next q) = P.cornerOffset v q * P.segment v q := by
  rcases q with ⟨c,i,j⟩
  fin_cases j
  · simp [next,cornerOffset,segment]
  · simp [next,cornerOffset,segment]
  · simpa [next,cornerOffset,segment] using IntegralIncidence.group_prefix_rotate
      (fun i => signed v (P.side c i)) (h c) i

lemma next_next_ne (q : P.Position) : P.next (P.next q) ≠ q := by
  rcases q with ⟨c,i,j⟩
  intro h
  have hh := congrArg (fun a : P.Position => a.2.2.val) h
  fin_cases j <;> simp [next] at hh

lemma base_ne_next (q : P.Position) : P.base q ≠ P.base (P.next q) := by
  rw [base_next]
  rcases q with ⟨c,i,j⟩
  rcases he : P.side c i with ⟨e,b⟩
  fin_cases j <;> cases b <;> simp [base,dartStart,he]

variable [DecidableEq E]

/-- Only the middle third of each graph edge carries its original voltage. -/
def graphValue : (V ⊕ (E × Bool)) → (V ⊕ (E × Bool)) → G
  | .inr (e,a), .inr (f,b) => if e = f ∧ a ≠ b then signed v (e,a) else 1
  | _,_ => 1

lemma graphValue_self (a : (V ⊕ (E × Bool))) : graphValue (V := V) v a a = 1 := by
  rcases a with a|⟨e,b⟩ <;> simp [graphValue]

lemma graphValue_reverse (a b : (V ⊕ (E × Bool))) : graphValue (V := V) v b a = (graphValue (V := V) v a b)⁻¹ := by
  rcases a with a|⟨e,a⟩ <;> rcases b with b|⟨f,b⟩ <;> try simp [graphValue]
  by_cases h : e = f
  · subst f; cases a <;> cases b <;> simp [signed]
  · simp [h,Ne.symm h]

variable [DecidableEq V] [DecidableEq C]

/-- The collar and cap formulas retain each occurrence's independent cornerOffset. -/
def value : P.Vertex → P.Vertex → G
  | .inl a, .inl b => graphValue (V := V) v a b
  | .inr (.inr q), .inl b => if P.graph b = P.base (P.next q) then P.segment v q else 1
  | .inl a, .inr (.inr q) => (if P.graph a = P.base (P.next q) then P.segment v q else 1)⁻¹
  | .inr (.inr q), .inr (.inr r) =>
      if r = P.next q then P.segment v q else if q = P.next r then (P.segment v r)⁻¹ else 1
  | .inr (.inl c), .inr (.inr q) => if c = q.1 then P.cornerOffset v q else 1
  | .inr (.inr q), .inr (.inl c) => (if c = q.1 then P.cornerOffset v q else 1)⁻¹
  | _,_ => 1

lemma value_self (a : P.Vertex) : P.value v a a = 1 := by
  rcases a with a|(c|q)
  · exact graphValue_self (V := V) v a
  · rfl
  · simp [value,Ne.symm (P.next_ne q)]

lemma value_reverse (a b : P.Vertex) : P.value v b a = (P.value v a b)⁻¹ := by
  rcases a with a|(c|q) <;> rcases b with b|(d|r) <;> first | exact graphValue_reverse v _ _ | simp only [value,inv_inv,inv_one]
  by_cases h : r = P.next q
  · subst r
    simp [Ne.symm (P.next_next_ne q)]
  · by_cases h' : q = P.next r
    · subst q; simp [h]
    · simp [h,h']

omit [DecidableEq V] [DecidableEq E] [DecidableEq C] in
lemma base_graph (q : P.Position) : ∃ b : V ⊕ (E × Bool), P.base q = P.graph b := by
  dsimp [base,dartStart]
  split_ifs <;> exact ⟨_,rfl⟩

lemma value_outer_base (q : P.Position) : P.value v (P.outer q) (P.base q) = 1 := by
  obtain ⟨b,hb⟩ := P.base_graph q
  have hn := P.base_ne_next q
  rw [hb] at hn ⊢
  simp [value,hn]

lemma value_outer_nextbase (q : P.Position) :
    P.value v (P.outer q) (P.base (P.next q)) = P.segment v q := by
  obtain ⟨b,hb⟩ := P.base_graph (P.next q)
  rw [hb]
  simp [value,hb]

lemma value_outer_next (q : P.Position) :
    P.value v (P.outer q) (P.outer (P.next q)) = P.segment v q := by simp [value]

lemma value_apex_outer (q : P.Position) :
    P.value v (P.apex q.1) (P.outer q) = P.cornerOffset v q := by simp [value]

lemma value_base_next (q : P.Position) :
    P.value v (P.base q) (P.base (P.next q)) = P.segment v q := by
  rw [base_next]
  rcases q with ⟨c,i,j⟩
  fin_cases j <;> simp [base,dartStart,value,graphValue,segment]

lemma collar_ordered (h : ∀ c, (List.ofFn (fun i => signed v (P.side c i))).prod = 1)
    (q : P.Position) :
    P.value v (P.outer q) (P.base q) * P.value v (P.base q) (P.base (P.next q)) =
      P.value v (P.outer q) (P.base (P.next q)) ∧
    P.value v (P.outer q) (P.outer (P.next q)) * P.value v (P.outer (P.next q)) (P.base (P.next q)) =
      P.value v (P.outer q) (P.base (P.next q)) ∧
    P.value v (P.outer q) (P.outer (P.next q)) * P.value v (P.outer (P.next q)) (P.apex q.1) =
      P.value v (P.outer q) (P.apex q.1) := by
  refine ⟨by simp [value_outer_base,value_base_next,value_outer_nextbase],
    by simp [value_outer_next,value_outer_base,value_outer_nextbase],?_⟩
  have hc : (P.next q).1 = q.1 := rfl
  rw [value_outer_next,P.value_reverse v (P.apex q.1) (P.outer (P.next q)),
    P.value_reverse v (P.apex q.1) (P.outer q)]
  rw [← hc, value_apex_outer,hc,value_apex_outer,cornerOffset_next P v h]
  simp

lemma facet_flat (h : ∀ c, (List.ofFn (fun i => signed v (P.side c i))).prod = 1)
    (f : P.Facet) {a b c : P.Vertex} (ha : a ∈ P.facet f) (hb : b ∈ P.facet f)
    (hc : c ∈ P.facet f) : P.value v a b * P.value v b c = P.value v a c := by
  cases f with
  | inl e =>
    dsimp [facet,graphFace] at ha hb hc
    split_ifs at ha hb hc <;> exact flat_two (P.value v) (P.value_self v) (P.value_reverse v) ha hb hc
  | inr q =>
    obtain ⟨h0,h1,h2⟩ := P.collar_ordered v h q.1
    dsimp [facet,collarFace] at ha hb hc
    split_ifs at ha hb hc
    · exact flat_three (P.value v) (P.value_self v) (P.value_reverse v) h0 ha hb hc
    · exact flat_three (P.value v) (P.value_self v) (P.value_reverse v) h1 ha hb hc
    · exact flat_three (P.value v) (P.value_self v) (P.value_reverse v) h2 ha hb hc

/-- Every literal source relation gives a genuine topological voltage cover of
its finite simplicial mapping-cylinder realization. -/
def voltage (h : ∀ c, (List.ofFn (fun i => signed v (P.side c i))).prod = 1) :
    Voltage P.complex G where
  value := P.value v
  self := P.value_self v
  triangle a b c ht := by
    rcases ht.2 with hsmall|⟨f,hf⟩
    · have hab : a = b := Finset.card_le_one.mp hsmall a (by simp) b (by simp)
      have hbc : b = c := Finset.card_le_one.mp hsmall b (by simp) c (by simp)
      subst b; subst c
      simp [value_self]
    · exact P.facet_flat v h f (hf (by simp)) (hf (by simp)) (hf (by simp))

end HyperbolicObstruction.FinitePolygonModel.Data
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FinitePolyhedronDeck
attribute [-instance] _root_.OAI.HyperbolicObstruction.FinitePolyhedron.openStar_contractible _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal voltage cover has a free transitive deck action. This supplies
an actual quotient covering to Mathlib's monodromy theorems. -/
noncomputable section

open scoped Topology
open Set
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

lemma chart_deck (i : V) (g : G) (e : v.TotalSpace) :
    v.core.localTriv i (g • e) = ((v.core.localTriv i e).1,g * (v.core.localTriv i e).2) := by
  change (e.proj,(g * v.coordinate e) * v.value _ i) =
    (e.proj,g * (v.coordinate e * v.value _ i))
  rw [mul_assoc]
  rfl

instance deckContinuous : ContinuousConstSMul G v.TotalSpace where
  continuous_const_smul g := by
    apply continuous_iff_continuousAt.mpr
    intro e
    let i := v.core.indexAt e.proj
    let t := v.core.localTriv i
    have he : e.proj ∈ t.baseSet := v.core.mem_baseSet_at e.proj
    apply t.continuousAt_of_comp_left
    · exact v.core.continuous_proj.continuousAt
    · exact he
    · have ht : ContinuousAt t e := t.continuousAt (t.mem_source.mpr he)
      have hg : Continuous (fun a : G => g * a) := continuous_of_discreteTopology
      have hc := ht.fst.prodMk (hg.continuousAt.comp ht.snd)
      convert hc using 1
      all_goals try with_reducible_and_instances rfl
      funext z
      exact v.chart_deck i g z

lemma same_fiber_iff_orbit (e f : v.TotalSpace) :
    v.proj e = v.proj f ↔ e ∈ MulAction.orbit G f := by
  constructor
  · intro he
    refine ⟨v.coordinate e * (v.coordinate f)⁻¹,?_⟩
    apply v.totalSpace_ext
    · exact he.symm
    · rw [deck_coordinate,mul_assoc,inv_mul_cancel,mul_one]
  · rintro ⟨g,rfl⟩
    rfl

lemma disjoint_deck_neighborhood (e : v.TotalSpace) :
    ∃ U ∈ 𝓝 e, ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1 := by
  let t := v.core.localTriv (v.core.indexAt e.proj)
  have he : e ∈ t.source := t.mem_source.mpr (v.core.mem_baseSet_at e.proj)
  let U : Set v.TotalSpace := t.source ∩ (fun z => (t z).2) ⁻¹' {(t e).2}
  have hopen : IsOpen U := t.continuousOn.snd.isOpen_inter_preimage t.open_source (isOpen_discrete _)
  refine ⟨U,hopen.mem_nhds ⟨he,rfl⟩,?_⟩
  intro g hg
  obtain ⟨z,⟨y,hy,rfl⟩,hz⟩ := hg
  have hy' : (t y).2 = (t e).2 := hy.2
  have hz' : (t (g • y)).2 = (t e).2 := hz.2
  rw [chart_deck] at hz'
  change g * (t y).2 = (t e).2 at hz'
  rw [hy'] at hz'
  exact mul_right_cancel (hz'.trans (one_mul _).symm)

lemma isQuotientCoveringMap : IsQuotientCoveringMap v.proj G where
  toIsQuotientMap := v.isCoveringMap.isQuotientMap v.proj_surjective
  continuous_const_smul g := continuous_const_smul g
  apply_eq_iff_mem_orbit := v.same_fiber_iff_orbit _ _
  disjoint := v.disjoint_deck_neighborhood

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FinitePolyhedronMonodromy
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual path-homotopy invariance of edge voltages, obtained from the
constructed covering and its literal charts. -/
noncomputable section

open scoped Topology
open Set
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

lemma chartFiber_change (x : Carrier K) {a b : V}
    (ha : x ∈ openStar K a) (hb : x ∈ openStar K b) (g : G) :
    v.chartFiber b x (g * v.value a b) = v.chartFiber a x g := by
  apply Subtype.ext
  apply v.totalSpace_ext
  · rfl
  change (g * v.value a b) * v.value b (v.core.indexAt x) = g * v.value a (v.core.indexAt x)
  rw [mul_assoc,v.triangle a b _ (triangle_of_positive K x ha hb (v.core.mem_baseSet_at x))]

def liftInChart {x y : Carrier K} (a : V) (p : Path x y)
    (hp : ∀ t, p t ∈ openStar K a) (g : G) :
    Path (v.inChart a x g) (v.inChart a y g) where
  toFun t := v.inChart a (p t) g
  continuous_toFun := (v.core.localTriv a).toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
    (p.continuous.prodMk continuous_const) (fun t => (v.core.localTriv a).mem_target.mpr (hp t))
  source' := by rw [p.source]
  target' := by rw [p.target]

lemma monodromy_inChart {x y : Carrier K} (a : V) (p : Path x y)
    (hp : ∀ t, p t ∈ openStar K a) (g : G) :
    v.isCoveringMap.monodromy (.mk p) (v.chartFiber a x g) = v.chartFiber a y g := by
  apply v.isCoveringMap.monodromy_eq_of_map_eq (.mk (v.liftInChart a p hp g))
  rfl

lemma monodromy_starPath (a : V) (x : Carrier K) (hx : x ∈ openStar K a) (g : G) :
    v.isCoveringMap.monodromy (.mk (starPath K a x hx)) (v.vertexFiber a g) =
      v.chartFiber a x g := by
  simpa only [chartFiber_vertex] using v.monodromy_inChart a (starPath K a x hx)
    (starPath_mem K a x hx) g

lemma monodromy_symm {x y : Carrier K} (p : Path.Homotopic.Quotient x y)
    (e : v.proj ⁻¹' {x}) :
    v.isCoveringMap.monodromy p.symm (v.isCoveringMap.monodromy p e) = e := by
  rw [←v.isCoveringMap.monodromy_trans_apply,Path.Homotopic.Quotient.trans_symm,
    v.isCoveringMap.monodromy_refl]
  rfl

/-- The midpoint lies in both endpoint stars, even for a collapsed edge. -/
def edgeMid {a b : V} (h : {a,b} ∈ K.faces) : Carrier K :=
  edgePath K h ⟨1/2,by norm_num,by norm_num⟩

lemma edgeMid_left {a b : V} (h : {a,b} ∈ K.faces) :
    edgeMid h ∈ openStar K a := by
  change 0 < (AffineMap.lineMap (vertex K a).val (vertex K b).val (1/2 : ℝ)) a
  rw [AffineMap.lineMap_apply_module]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have ha : (vertex K a).val a = 1 := by simp [vertex]
  rw [ha]
  have hb := (vertex K b).property.1 a
  linarith

lemma edgeMid_right {a b : V} (h : {a,b} ∈ K.faces) :
    edgeMid h ∈ openStar K b := by
  change 0 < (AffineMap.lineMap (vertex K a).val (vertex K b).val (1/2 : ℝ)) b
  rw [AffineMap.lineMap_apply_module]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have hb : (vertex K b).val b = 1 := by simp [vertex]
  rw [hb]
  have ha := (vertex K a).property.1 b
  linarith

lemma monodromy_edge {a b : V} (h : {a,b} ∈ K.faces) (g : G) :
    v.isCoveringMap.monodromy (.mk (edgePath K h)) (v.vertexFiber a g) =
      v.vertexFiber b (g * v.value a b) := by
  let x : Carrier K := edgeMid h
  have ha : x ∈ openStar K a := edgeMid_left h
  have hb : x ∈ openStar K b := edgeMid_right h
  have hh := Path.Homotopic.Quotient.eq.mpr (radial_bridge K x ha hb)
  rw [←hh,Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.mk_symm,
    v.isCoveringMap.monodromy_trans_apply,v.monodromy_starPath]
  rw [←v.chartFiber_change x ha hb g]
  rw [←v.monodromy_starPath b x hb (g * v.value a b),v.monodromy_symm]

namespace EdgeChain
variable {v} {a b : V}

lemma monodromy (q : FinitePolyhedron.EdgeChain K a b) (g : G) :
    v.isCoveringMap.monodromy q.pathClass (v.vertexFiber a g) =
      v.vertexFiber b (g * eval v q) := by
  induction q generalizing g with
  | nil a => simp [FinitePolyhedron.EdgeChain.pathClass_nil,v.isCoveringMap.monodromy_refl]
  | cons h q ih =>
    rw [FinitePolyhedron.EdgeChain.pathClass_cons,v.isCoveringMap.monodromy_trans_apply,
      v.monodromy_edge,ih,eval_cons,mul_assoc]
end EdgeChain

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FinitePolyhedronPathAlgebra
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The triangle relations and rooted path groupoid calculations in the
actual realization. -/
noncomputable section

open Set
attribute [local instance] Classical.propDecidable
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [Fintype V] [DecidableEq V] (K : AbstractSimplicialComplex V)

lemma edgePath_triangle {a b c : V} (hs : {a,b,c} ∈ K.faces)
    (hab : {a,b} ∈ K.faces) (hbc : {b,c} ∈ K.faces) (hac : {a,c} ∈ K.faces) :
    ((edgePath K hab).trans (edgePath K hbc)).Homotopic (edgePath K hac) := by
  apply homotopic_in_face K hs
  · intro t
    have ht := mem_range_self (f := (edgePath K hab).trans (edgePath K hbc)) t
    rw [Path.trans_range] at ht
    rcases ht with ⟨u,hu⟩|⟨u,hu⟩ <;> rw [←hu]
    · unfold edgePath facePath
      exact straight_mem_face K _ (vertex_mem_simplex K (by simp)) (vertex_mem_simplex K (by simp)) u
    · unfold edgePath facePath
      exact straight_mem_face K _ (vertex_mem_simplex K (by simp)) (vertex_mem_simplex K (by simp)) u
  · intro t
    unfold edgePath facePath
    exact straight_mem_face K _ (vertex_mem_simplex K (by simp)) (vertex_mem_simplex K (by simp)) t

namespace RootedPaths
variable {K} (o : V) (R : ∀ a : V, Path.Homotopic.Quotient (vertex K o) (vertex K a))

omit [DecidableEq V] in
lemma based_trans {a b c : V} (p : Path.Homotopic.Quotient (vertex K a) (vertex K b))
    (q : Path.Homotopic.Quotient (vertex K b) (vertex K c)) :
    based o R (p.trans q) = based o R p * based o R q := by
  apply MulOpposite.unop_injective
  change (R a).trans ((p.trans q).trans (R c).symm) =
    ((R a).trans (p.trans (R b).symm)).trans ((R b).trans (q.trans (R c).symm))
  simp only [Path.Homotopic.Quotient.trans_assoc]
  have hc : (R b).symm.trans ((R b).trans (q.trans (R c).symm)) = q.trans (R c).symm := by
    rw [←Path.Homotopic.Quotient.trans_assoc,Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.refl_trans]
  rw [hc]

omit [DecidableEq V] in
lemma based_route (hR : R o = .refl _) (a : V) : based o R (R a) = 1 := by
  apply MulOpposite.unop_injective
  change (R o).trans ((R a).trans (R a).symm) = .refl _
  rw [hR,Path.Homotopic.Quotient.trans_symm,Path.Homotopic.Quotient.refl_trans]

omit [DecidableEq V] in
lemma based_loop (hR : R o = .refl _) (p : FundamentalGroup (Carrier K) (vertex K o)) :
    based o R p = MulOpposite.op p := by
  apply MulOpposite.unop_injective
  change (R o).trans (p.trans (R o).symm) = p
  rw [hR]
  have hr : (Path.Homotopic.Quotient.refl (vertex K o)).symm = .refl _ := rfl
  rw [hr,Path.Homotopic.Quotient.trans_refl,Path.Homotopic.Quotient.refl_trans]

lemma edgeLoop_of_edge {a b : V} (h : {a,b} ∈ K.faces) :
    edgeLoop o R a b = based o R (.mk (edgePath K h)) := dite_eq_left h

/-- The actual triangle disks imply a group-valued flat cocycle. -/
def voltage : Voltage K (PiOne (K := K) o) where
  value := edgeLoop o R
  self a := by rw [edgeLoop_of_edge o R (edge_self K a),edgePath_self]; exact based_refl o R a
  triangle a b c h := by
    have hab := edge_of_subset K h (a := a) (b := b) (by simp) (by simp)
    have hbc := edge_of_subset K h (a := b) (b := c) (by simp) (by simp)
    have hac := edge_of_subset K h (a := a) (b := c) (by simp) (by simp)
    rw [edgeLoop_of_edge o R hab,edgeLoop_of_edge o R hbc,edgeLoop_of_edge o R hac,
      ←based_trans]
    congr 1
    exact Path.Homotopic.Quotient.eq.mpr (edgePath_triangle K h hab hbc hac)

lemma eval_chain {a b : V} (p : EdgeChain K a b) :
    Voltage.EdgeChain.eval (voltage o R) p = based o R p.pathClass := by
  induction p with
  | nil a => exact (based_refl o R a).symm
  | @cons a b c h p ih =>
    rw [Voltage.EdgeChain.eval_cons,ih,EdgeChain.pathClass_cons,based_trans]
    congr 1
    exact edgeLoop_of_edge o R h
end RootedPaths

end HyperbolicObstruction.FinitePolyhedron
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_HSpaceFundamental
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual fundamental group of an H-space is abelian. The proof uses the
relative unit homotopies, not an assumed pi-2 comparison theorem. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.HSpaceFundamental
open Path.Homotopic
variable {X : Type*} [TopologicalSpace X] [HSpace X]
local notation "e" => (HSpace.e : X)

/-- The group multiplication is the original fundamental-group multiplication. -/
@[instance_reducible] def commGroup : CommGroup (FundamentalGroup X e) :=
  EckmannHilton.commGroup
    (show EckmannHilton.IsUnital (@combine X _ _) 1 from
      { left_id := combine_one_left, right_id := combine_one_right }) combine_interchange

end HyperbolicObstruction.HSpaceFundamental
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ProtectedNormal
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary
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

/-- A protected indexed side has no oppositely indexed side anywhere in the
input. A single oriented exterior polygon satisfies this condition literally. -/
def Unopposed (keep : S → Prop) : Prop :=
  ∀ x y : P.Dart, keep (P.index x) → P.index y ≠ T.opposite (P.index x)

structure Preserves (keep : S → Prop) (Q : WalkPicture.{u} T) extends P.Survives Q where
  complete : ∀ x, keep (P.index x) → ∃ y, toSurvives.map y = x

variable {P}
def Preserves.trans {Q R : WalkPicture.{u} T} {keep : S → Prop}
    (hPQ : P.Preserves keep Q) (hQR : Q.Preserves keep R) : P.Preserves keep R := by
  refine ⟨Survives.trans P hPQ.toSurvives hQR.toSurvives,?_⟩
  intro x hx
  obtain ⟨y,hy⟩ := hPQ.complete x hx
  obtain ⟨z,hz⟩ := hQR.complete y (by rw [hPQ.index,hy]; exact hx)
  exact ⟨z,by change hPQ.map (hQR.map z) = x; rw [hz,hy]⟩

lemma Survives.unopposed {Q : WalkPicture.{u} T} {keep : S → Prop}
    (hPQ : P.Survives Q) (h : P.Unopposed keep) : Q.Unopposed keep := by
  intro x y hx hy
  apply h (hPQ.map x) (hPQ.map y)
  · rwa [← hPQ.index]
  · rw [← hPQ.index,← hPQ.index]
    exact hy

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureSum
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary
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
variable {D E : Type*} [DecidableEq D] [DecidableEq E] [Fintype D] [Fintype E]

namespace PictureMap
variable (M : PictureMap D) (N : PictureMap E)

/-- Literal disjoint union of polygon side-pairings. -/
def sum : PictureMap (D ⊕ E) where
  face := Equiv.sumCongr M.face N.face
  edge := Equiv.sumCongr M.edge N.edge
  edge_sq := by
    apply Equiv.ext
    intro x; cases x <;> simp [M.edge_edge,N.edge_edge]
  edge_ne := by
    intro x h; cases x with
    | inl x => exact M.edge_ne x (Sum.inl.inj h)
    | inr x => exact N.edge_ne x (Sum.inr.inj h)

omit [DecidableEq D] [DecidableEq E] [Fintype D] [Fintype E] in
lemma sum_vertex : (M.sum N).vertex = Equiv.sumCongr M.vertex N.vertex := by
  apply Equiv.ext
  intro x; cases x <;> rfl

def sumClassifier : D ⊕ E → Quotient M.components ⊕ Quotient N.components :=
  Sum.map (Quotient.mk _) (Quotient.mk _)

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordPictureAppend
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
namespace IsBoundary
variable {D : Type*} [DecidableEq D] {f : Perm D} {xs ys : List D}
lemma splice_away (hx : IsBoundary f xs) {a b : D} (ha : a ∉ xs) (hb : b ∉ xs) :
    IsBoundary (f * swap a b) xs := by
  refine ⟨hx.nodup,?_⟩
  intro x hm
  have hxa : x ≠ a := fun h => ha (h ▸ hm)
  have hxb : x ≠ b := fun h => hb (h ▸ hm)
  rw [mul_apply,swap_apply_of_ne_of_ne hxa hxb]
  exact hx.turn x hm
end IsBoundary
end HyperbolicObstruction.PictureSwitch

end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordPictureCell
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
variable {S L V B : Type*} [DecidableEq S] [AddCommMonoid B]
namespace CellTarget
variable (T : CellTarget S L V B)

omit [DecidableEq S] in
lemma opposite_inv_next (s : S) : T.opposite (T.next⁻¹ s) = T.next (T.opposite s) := by
  have h := semiconj_perm_inv T.reverse_next s
  simpa only [inv_inv] using h

omit [DecidableEq S] in
lemma reverse_boundary_labels {xs : List S} :
    (xs.reverse.map T.opposite).map T.edge = (xs.map (T.rev ∘ T.edge)).reverse := by
  simp only [List.map_map,List.map_reverse,Function.comp_def,T.edge_opposite]

end CellTarget
end HyperbolicObstruction.PictureSwitch

end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RankSelection
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace FiniteLaw

lemma bernoulliProduct_sum_expect {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (p : I → ℝ) (q : J → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1) (hq : ∀ i, q i ∈ Set.Icc (0:ℝ) 1)
    (f : (I ⊕ J → Bool) → ℝ) :
    (bernoulliProduct (Sum.elim p q) (fun i => by cases i <;> simp_all)).expect f =
      ((bernoulliProduct p hp).prod (bernoulliProduct q hq)).expect
        (fun z => f (Sum.elim z.1 z.2)) := by
  unfold expect
  rw [← (Equiv.sumArrowEquivProdArrow I J Bool).symm.sum_comp
    (fun w => (bernoulliProduct (Sum.elim p q) _).mass w * f w)]
  apply Finset.sum_congr rfl
  intro z _
  simp only [bernoulliProduct,prod,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr]
  rfl

end FiniteLaw
end HyperbolicObstruction
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonCornerPrimitive
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! Explicit cyclic antiderivatives for the literal threefold-subdivided
polygon corners. This retains the actual constructor `Position`. -/
noncomputable section
namespace HyperbolicObstruction.FinitePolygonModel.Data
open CyclicTriangleBoundary
variable {V E C B : Type*} [AddCommGroup B]
  (P : Data V E C)

def cornerPrimitive (f : P.Position → B) (q : P.Position) : B :=
  cyclePrimitive (fun i => ∑ j : Fin 3, f ⟨q.1,(i,j)⟩) q.2.1 -
    ∑ j ∈ Finset.Iio q.2.2, f ⟨q.1,(q.2.1,j)⟩

end HyperbolicObstruction.FinitePolygonModel.Data
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonLiftedCochain
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Oriented cochains on the literal lifted triangulation, retaining all
independent sheet labels. Negative edges use the reverse initial sheet. -/
noncomputable section

namespace HyperbolicObstruction.FinitePolygonModel.Data
variable {V E C G B : Type*} [Fintype V] [Fintype E] [Fintype C]
  [DecidableEq V] [DecidableEq E] [DecidableEq C] [Group G] [AddCommGroup B]
  (P : Data V E C) (v : E → G)
  (w : G × E → B) (diag outer apex : G → P.Position → B)

def graphCochain (g : G) : GraphVertex (V := V) (E := E) → GraphVertex (V := V) (E := E) → B
  | .inr (e,a), .inr (f,b) => if e = f ∧ a ≠ b then
      if a then w (g,e) else -w (g*(v e)⁻¹,e) else 0
  | _,_ => 0

def liftedCochain (g : G) : P.Vertex → P.Vertex → B
  | .inl a, .inl b => graphCochain v w g a b
  | .inr (.inr q), .inl b => if P.graph b = P.base (P.next q) then diag g q else 0
  | .inl a, .inr (.inr q) =>
      if P.graph a = P.base (P.next q) then -diag (g*(P.segment v q)⁻¹) q else 0
  | .inr (.inr q), .inr (.inr r) =>
      if r = P.next q then outer g q else if q = P.next r then -outer (g*(P.segment v r)⁻¹) r else 0
  | .inr (.inl c), .inr (.inr q) => if c = q.1 then apex g q else 0
  | .inr (.inr q), .inr (.inl c) => if c = q.1 then -apex (g*(P.cornerOffset v q)⁻¹) q else 0
  | _,_ => 0

omit [Fintype V] [Fintype E] [DecidableEq V] in
lemma graphCochain_reverse (g : G) (a b : GraphVertex (V := V) (E := E)) :
    graphCochain v w (g*graphValue v a b) b a = -graphCochain v w g a b := by
  rcases a with a|⟨e,a⟩ <;> rcases b with b|⟨f,b⟩ <;> try simp [graphCochain,graphValue]
  by_cases he : e = f
  · subst f
    cases a <;> cases b <;> simp [signed,mul_assoc]
  · simp [he,Ne.symm he]

omit [Fintype V] [Fintype E] [Fintype C] in
lemma liftedCochain_self (g : G) (a : P.Vertex) : P.liftedCochain v w diag outer apex g a a = 0 := by
  rcases a with a|(c|q)
  · rcases a with a|⟨e,b⟩ <;> simp [liftedCochain,graphCochain]
  · rfl
  · simp [liftedCochain,Ne.symm (P.next_ne q)]

omit [Fintype V] [Fintype E] [Fintype C] in
lemma liftedCochain_reverse (g : G) (a b : P.Vertex) :
    P.liftedCochain v w diag outer apex (g*P.value v a b) b a =
      -P.liftedCochain v w diag outer apex g a b := by
  rcases a with a|(c|q) <;> rcases b with b|(d|r)
  · exact graphCochain_reverse v w g a b
  · simp [liftedCochain]
  · simp only [liftedCochain,value]
    split_ifs <;> simp
  · simp [liftedCochain]
  · simp [liftedCochain]
  · simp only [liftedCochain,value]
    split_ifs <;> simp [mul_assoc]
  · simp only [liftedCochain,value]
    split_ifs <;> simp
  · simp only [liftedCochain,value]
    split_ifs <;> simp
  · by_cases hr : r = P.next q
    · subst r
      simp [liftedCochain,value,Ne.symm (P.next_next_ne q),mul_assoc]
    · by_cases hq : q = P.next r
      · subst q
        simp [liftedCochain,value,hr]
      · simp [liftedCochain,hr,hq]

omit [Fintype V] [Fintype E] [Fintype C] in
lemma cochain_outer_base (g : G) (q : P.Position) :
    P.liftedCochain v w diag outer apex g (P.outer q) (P.base q) = 0 := by
  obtain ⟨b,hb⟩ := P.base_graph q
  have hn := P.base_ne_next q
  rw [hb] at hn ⊢
  simp [liftedCochain,hn]
omit [Fintype V] [Fintype E] [Fintype C] in
lemma cochain_outer_nextbase (g : G) (q : P.Position) :
    P.liftedCochain v w diag outer apex g (P.outer q) (P.base (P.next q)) = diag g q := by
  obtain ⟨b,hb⟩ := P.base_graph (P.next q)
  rw [hb]
  simp [liftedCochain,hb]
omit [Fintype V] [Fintype E] [Fintype C] in
lemma cochain_outer_next (g : G) (q : P.Position) :
    P.liftedCochain v w diag outer apex g (P.outer q) (P.outer (P.next q)) = outer g q := by
  simp [liftedCochain]
omit [Fintype V] [Fintype E] [Fintype C] in
lemma cochain_outer_apex (g : G) (q : P.Position) :
    P.liftedCochain v w diag outer apex g (P.outer q) (P.apex q.1) = -apex (g*(P.cornerOffset v q)⁻¹) q := by
  simp [liftedCochain]

end HyperbolicObstruction.FinitePolygonModel.Data
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonTriangleCochains
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cochain extension with literal initial-sheet coordinates for every collar
triangle. Its only algebraic input is the precise polygon boundary equation. -/
noncomputable section

namespace HyperbolicObstruction.FinitePolygonModel.Data
variable {V E C G B : Type*}
  [DecidableEq V] [DecidableEq E] [DecidableEq C] [Group G] [AddCommGroup B]
  (P : Data V E C) (v : E → G) (w : G × E → B)

def segmentCochain (g : G) (q : P.Position) : B :=
  if q.2.2.val = 1 then signedCochain v w g (P.side q.1 q.2.1) else 0

lemma cochain_base_next (diag outer apex : G → P.Position → B) (g : G) (q : P.Position) :
    P.liftedCochain v w diag outer apex g (P.base q) (P.base (P.next q)) = P.segmentCochain v w g q := by
  rw [P.base_next]
  rcases q with ⟨c,i,j⟩
  fin_cases j <;> cases hb : (P.side c i).2 <;>
    simp [base,dartStart,liftedCochain,graphCochain,segmentCochain,signedCochain,hb]

variable (T : G → P.Position → Fin 3 → B)
def triangleWeight (g : G) (q : P.Position) : B := T g q 0 - T g q 1 + T g q 2

def correctionDiagonal (g : G) (q : P.Position) : B := P.segmentCochain v w g q - T g q 0
def correctionOuter (g : G) (q : P.Position) : B := P.correctionDiagonal v w T g q + T g q 1
def correctionIncrement (d : G) (q : P.Position) : B :=
  P.triangleWeight T (d*P.cornerOffset v q) q - P.segmentCochain v w (d*P.cornerOffset v q) q

def correctionApex (d : G) (q : P.Position) : B := P.cornerPrimitive (P.correctionIncrement v w T d) q

def triangleCochain (g : G) (a b : P.Vertex) : B := P.liftedCochain v w
  (P.correctionDiagonal v w T) (P.correctionOuter v w T) (P.correctionApex v w T) g a b

variable (hc : ∀ c, (List.ofFn (fun i => signed v (P.side c i))).prod = 1)
variable (hw : ∀ d c, (∑ i : Fin (P.size c),
    signedCochain v w (d*((List.ofFn (fun i => signed v (P.side c i))).take i.val).prod) (P.side c i)) =
    ∑ i : Fin (P.size c), ∑ j : Fin 3,
      P.triangleWeight T (d*P.cornerOffset v ⟨c,(i,j)⟩) ⟨c,(i,j)⟩)

omit [DecidableEq V] [DecidableEq E] [DecidableEq C] in
include hw in
lemma correctionIncrement_sum (d : G) (c : C) :
    ∑ i : Fin (P.size c), ∑ j : Fin 3, P.correctionIncrement v w T d ⟨c,(i,j)⟩ = 0 := by
  simp only [correctionIncrement,Finset.sum_sub_distrib]
  rw [←hw d c]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro i hi
  simp [Fin.sum_univ_three,segmentCochain,cornerOffset]

end HyperbolicObstruction.FinitePolygonModel.Data
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SimplexCoordinates
attribute [-instance] _root_.OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.deckContinuous _root_.OAI.HyperbolicObstruction.FinitePolyhedron.openStar_contractible _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! Explicit finite simplex coordinates, with the actual barycentric subspace
topology. No CW coordinate comparison is assumed. -/
noncomputable section
open scoped Topology
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [DecidableEq V] {n : ℕ}

lemma barycentric_off {e : Fin n → V} (z : Fin n → ℝ) {j : V}
    (hj : j ∉ Finset.univ.image e) : barycentric e z j = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  exact ite_eq_right (fun h => hj (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,h⟩))

variable [Fintype V]

lemma barycentric_mem (e : Fin n → V)
    (z : {weights : Fin n → ℝ // (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}) :
    barycentric e z ∈ simplex (Finset.univ.image e) := by
  refine ⟨fun j => Finset.sum_nonneg (fun i hi => ?_),?_,?_⟩
  · split_ifs <;> first | exact z.property.1 i | exact le_refl 0
  · exact (barycentric_sum e z).trans z.property.2
  · exact fun j hj => barycentric_off z.val hj

variable (K : AbstractSimplicialComplex V)
/-- The closed simplex in the carrier and its ambient barycentric subtype
carry exactly the same topology. -/
def closedSimplexHomeomorph {s : Finset V} (hs : s ∈ K.faces) :
    simplex s ≃ₜ {x : Carrier K // x.val ∈ simplex s} where
  toFun x := ⟨⟨x.val,simplex_subset_carrier K hs x.property⟩,x.property⟩
  invFun x := ⟨x.val.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

end HyperbolicObstruction.FinitePolyhedron
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

omit [DecidableEq V] in
lemma closedFace_isClosed (s : Finset V) : IsClosed (closedFace (K := K) s) :=
  (simplex_closed s).preimage continuous_subtype_val

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltageEdges
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal oriented edges and triangles of the genuine voltage cover. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

variable {v}
variable (v)

lemma edgePath_reverse {a b : V} (h : {a,b} ∈ K.faces) (t : I) :
    edgePath K (show {b,a} ∈ K.faces by simpa [Finset.pair_comm] using h) t =
      edgePath K h (unitInterval.symm t) := by
  apply Subtype.ext
  change AffineMap.lineMap (vertex K b).val (vertex K a).val (t : ℝ) =
    AffineMap.lineMap (vertex K a).val (vertex K b).val (1-(t:ℝ))
  exact AffineMap.lineMap_apply_one_sub _ _ _ |>.symm

lemma edgeLift_reverse {a b : V} (h : {a,b} ∈ K.faces) (g : G) (t : I) :
    v.edgeLift (show {b,a} ∈ K.faces by simpa [Finset.pair_comm] using h)
      (g * v.value a b) t = v.edgeLift h g (unitInterval.symm t) := by
  rw [edgeLift_apply,edgeLift_apply,edgePath_reverse]
  exact v.inChart_change_face h (a:=a) (b:=b) (by simp) (by simp) (edgePoint h (unitInterval.symm t)) g

lemma edgeLift_self (a : V) (g : G) (t : I) :
    v.edgeLift (edge_self K a) g t = v.vertexLift a g := by
  rw [edgeLift_apply,edgePath_self]
  change v.inChart a (vertex K a) g = _
  rw [inChart_vertex,v.self,mul_one]

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltageTriangles
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact triangular coordinates in the independent lifted cells. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
open TriangleSquare
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

variable {v}
def trianglePoint {a b c : V} (h : {a,b,c} ∈ K.faces) : C(Triangle,closedFace (K := K) {a,b,c}) := by
  let f : C(Triangle,simplex {a,b,c}) :=
    ⟨fun z => ⟨barycentric ![a,b,c] z, by
      have hz := barycentric_mem ![a,b,c] z
      rw [triangle_image] at hz
      exact hz⟩, by
      apply Continuous.subtype_mk
      exact (barycentric_continuous ![a,b,c]).comp continuous_subtype_val⟩
  exact (⟨closedSimplexHomeomorph K h,(closedSimplexHomeomorph K h).continuous⟩ : C(simplex {a,b,c},closedFace (K := K) {a,b,c})).comp f

lemma trianglePoint_bottom {a b c : V} (h : {a,b,c} ∈ K.faces) (s : I) :
    (trianglePoint h (quotient (s,0))).val =
      edgePath K (edge_of_subset K h (by simp) (by simp) : {a,b} ∈ K.faces) s := by
  apply Subtype.ext
  funext j
  change barycentric ![a,b,c] (quotient (s,0)).val j =
    (AffineMap.lineMap (vertex K a).val (vertex K b).val (s:ℝ)) j
  rw [quotient_zero]
  simp [barycentric,Fin.sum_univ_succ,AffineMap.lineMap_apply_module,vertex,Pi.single_apply,eq_comm]

lemma trianglePoint_left {a b c : V} (h : {a,b,c} ∈ K.faces) (s : I) :
    (trianglePoint h (quotient (0,s))).val =
      edgePath K (edge_of_subset K h (by simp) (by simp) : {a,c} ∈ K.faces) s := by
  apply Subtype.ext
  funext j
  change barycentric ![a,b,c] (quotient (0,s)).val j =
    (AffineMap.lineMap (vertex K a).val (vertex K c).val (s:ℝ)) j
  rw [quotient_left]
  simp [barycentric,Fin.sum_univ_succ,AffineMap.lineMap_apply_module,vertex,Pi.single_apply,eq_comm]

lemma trianglePoint_right {a b c : V} (h : {a,b,c} ∈ K.faces) (s : I) :
    (trianglePoint h (quotient (1,s))).val =
      edgePath K (edge_of_subset K h (by simp) (by simp) : {b,c} ∈ K.faces) s := by
  apply Subtype.ext
  funext j
  change barycentric ![a,b,c] (quotient (1,s)).val j =
    (AffineMap.lineMap (vertex K b).val (vertex K c).val (s:ℝ)) j
  rw [quotient_right]
  simp [barycentric,Fin.sum_univ_succ,AffineMap.lineMap_apply_module,vertex,Pi.single_apply,eq_comm]

variable (v)
def triangleLift {a b c : V} (h : {a,b,c} ∈ K.faces) (g : G) : C(Triangle,v.TotalSpace) :=
  (v.faceLift h (a:=a) (by simp) g).comp (trianglePoint h)

lemma triangleLift_bottom {a b c : V} (h : {a,b,c} ∈ K.faces) (g : G) (s : I) :
    v.triangleLift h g (quotient (s,0)) =
      v.edgeLift (edge_of_subset K h (by simp) (by simp) : {a,b} ∈ K.faces) g s := by
  change v.inChart a _ g = v.inChart a _ g
  rw [trianglePoint_bottom]
  rfl
lemma triangleLift_left {a b c : V} (h : {a,b,c} ∈ K.faces) (g : G) (s : I) :
    v.triangleLift h g (quotient (0,s)) =
      v.edgeLift (edge_of_subset K h (by simp) (by simp) : {a,c} ∈ K.faces) g s := by
  change v.inChart a _ g = v.inChart a _ g
  rw [trianglePoint_left]
  rfl
lemma triangleLift_right {a b c : V} (h : {a,b,c} ∈ K.faces) (g : G) (s : I) :
    v.triangleLift h g (quotient (1,s)) =
      v.edgeLift (edge_of_subset K h (by simp) (by simp) : {b,c} ∈ K.faces) (g*v.value a b) s := by
  rw [edgeLift_apply,←trianglePoint_right h]
  exact (v.inChart_change_face h (a:=a) (b:=b) (by simp) (by simp) (trianglePoint h (quotient (1,s))) g).symm

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonTriangles
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal ordered collar triangles and exhaustivity of their two-dimensional
faces. No uniqueness of polygon vertices is presumed. -/
noncomputable section

namespace HyperbolicObstruction.FinitePolygonModel.Data
open FinitePolyhedron FinitePolyhedron.Voltage
variable {V E C : Type*}
  [DecidableEq V] [DecidableEq E] [DecidableEq C] (P : Data V E C)

def collarB (q : P.Position) (j : Fin 3) : P.Vertex :=
  if j.val = 0 then P.base q else P.outer (P.next q)
def collarC (q : P.Position) (j : Fin 3) : P.Vertex :=
  if j.val = 2 then P.apex q.1 else P.base (P.next q)
lemma collarFace_eq (q : P.Position) (j : Fin 3) :
    P.collarFace q j = {P.outer q,P.collarB q j,P.collarC q j} := by
  fin_cases j <;> simp [collarFace,collarB,collarC]
lemma collar_mem (q : P.Position) (j : Fin 3) :
    {P.outer q,P.collarB q j,P.collarC q j} ∈ P.complex.faces := by
  rw [←P.collarFace_eq]
  exact P.facet_face (.inr (q,j))
omit [DecidableEq V] [DecidableEq E] [DecidableEq C] in
lemma collar_injective (q : P.Position) (j : Fin 3) :
    Function.Injective ![P.outer q,P.collarB q j,P.collarC q j] := by
  obtain ⟨a,ha⟩ := P.base_graph q
  obtain ⟨b,hb⟩ := P.base_graph (P.next q)
  have hn := P.base_ne_next q
  have hq := P.next_ne q
  fin_cases j <;> simp only [collarB,collarC]
  all_goals apply three_injective
  all_goals first
    | assumption
    | solve | simp [ha,hb,outer,apex,graph]
    | simpa [outer,eq_comm] using hq

end HyperbolicObstruction.FinitePolygonModel.Data
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

variable (z : v.TotalSpace)
structure EdgePrisms where
  H : ∀ {a b : V}, {a,b} ∈ K.faces → G → C(I × I,v.TotalSpace)
  initial : ∀ {a b} (h : {a,b} ∈ K.faces) g r, H h g (0,r) = v.edgeLift h g r
  final : ∀ {a b} (h : {a,b} ∈ K.faces) g r, H h g (1,r) = z
  agree : ∀ {a b c d} (h : {a,b} ∈ K.faces) (h' : {c,d} ∈ K.faces) g k t r s,
    v.edgeLift h g r = v.edgeLift h' k s → H h g (t,r) = H h' k (t,s)

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltageGraphHomotopy
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A coherent contraction of the actual lifted one-skeleton. The negative
orientation uses spatial reversal of the SAME square, not another choice. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

omit [Fintype V] [LinearOrder V] [TopologicalSpace G] [DiscreteTopology G] in
lemma value_reverse_mul {a b : V} (h : {a,b} ∈ K.faces) (g : G) :
    (g * v.value a b) * v.value b a = g := by
  rw [mul_assoc,v.reverse h,mul_inv_cancel,mul_one]

variable [SimplyConnectedSpace v.TotalSpace] (z : v.TotalSpace)
def vertexTrack (a : V) (g : G) : Path (v.vertexLift a g) z := by
  classical
  exact if h : v.vertexLift a g = z then (Path.refl z).cast h rfl
  else (PathConnectedSpace.joined (v.vertexLift a g) z).some

def rawEdgeHomotopy {a b : V} (h : {a,b} ∈ K.faces) (g : G) : C(I × I,v.TotalSpace) :=
  EdgeContraction.contraction (v.edgeLift h g) (v.vertexTrack z a g)
    (v.vertexTrack z b (g * v.value a b))

def edgeHomotopy {a b : V} (h : {a,b} ∈ K.faces) (g : G) : C(I × I,v.TotalSpace) :=
  if a = b then (v.vertexTrack z a g).toContinuousMap.comp (⟨Prod.fst,continuous_fst⟩ : C(I × I,I))
  else if a < b then v.rawEdgeHomotopy z h g
  else (v.rawEdgeHomotopy z (show {b,a} ∈ K.faces by simpa [Finset.pair_comm] using h)
    (g*v.value a b)).comp ⟨fun ts => (ts.1,unitInterval.symm ts.2),by fun_prop⟩

lemma edgeHomotopy_initial {a b : V} (h : {a,b} ∈ K.faces) (g : G) (s : I) :
    v.edgeHomotopy z h g (0,s) = v.edgeLift h g s := by
  unfold edgeHomotopy
  split_ifs with hab hlt
  · subst b
    change v.vertexTrack z a g 0 = _
    rw [Path.source]
    exact (v.edgeLift_self a g s).symm
  · exact EdgeContraction.contraction_initial _ _ _ s
  · change v.rawEdgeHomotopy z _ _ (0,unitInterval.symm s) = _
    rw [rawEdgeHomotopy,EdgeContraction.contraction_initial,v.edgeLift_reverse,unitInterval.symm_symm]

lemma edgeHomotopy_final {a b : V} (h : {a,b} ∈ K.faces) (g : G) (s : I) :
    v.edgeHomotopy z h g (1,s) = z := by
  unfold edgeHomotopy
  split_ifs
  · exact Path.target _
  · exact EdgeContraction.contraction_final _ _ _ s
  · exact EdgeContraction.contraction_final _ _ _ (unitInterval.symm s)

lemma edgeHomotopy_left {a b : V} (h : {a,b} ∈ K.faces) (g : G) (t : I) :
    v.edgeHomotopy z h g (t,0) = v.vertexTrack z a g t := by
  unfold edgeHomotopy
  split_ifs
  · rfl
  · exact EdgeContraction.contraction_left _ _ _ t
  · change v.rawEdgeHomotopy z _ _ (t,unitInterval.symm 0) = _
    rw [unitInterval.symm_zero,rawEdgeHomotopy,EdgeContraction.contraction_right,v.value_reverse_mul h]

lemma edgeHomotopy_right {a b : V} (h : {a,b} ∈ K.faces) (g : G) (t : I) :
    v.edgeHomotopy z h g (t,1) = v.vertexTrack z b (g*v.value a b) t := by
  unfold edgeHomotopy
  split_ifs with hab hlt
  · subst b
    change v.vertexTrack z a g t = v.vertexTrack z a (g*v.value a a) t
    rw [v.self a,mul_one]
  · exact EdgeContraction.contraction_right _ _ _ t
  · change v.rawEdgeHomotopy z _ _ (t,unitInterval.symm 1) = _
    rw [unitInterval.symm_one,rawEdgeHomotopy,EdgeContraction.contraction_left]

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltageEdgeCorrection
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose representatives of a directed pi2-cochain with LITERAL spatial
reversal, so corrected edge prisms agree as maps, not merely as classes. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
open HSpacePathObstruction
variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G) (z : v.TotalSpace)
local notation "e" => Path.refl z
abbrev LoopClass := FundamentalGroup (Path z z) e

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SquareBoundaryExtension
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four actual edge homotopies extend a square homotopy, with their literal
boundary formulas retained. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.SquareBoundaryExtension
attribute [local instance] Classical.propDecidable
variable {X : Type*} [TopologicalSpace X]

namespace Data
variable (D : Data (X := X))

def boundary : C(I × Cube.boundary (Fin 2),X) :=
  ClosedCoverGluing.glue face D.onFace D.agree face_cover face_closed (locallyFinite_of_finite _)

lemma boundary_eq (q : Fin 2 × Bool) (t : I) (z : Cube.boundary (Fin 2))
    (hz : z.val q.1 = endpoint q.2) :
    D.boundary (t,z) = D.side q (t,z.val (other q.1)) :=
  ClosedCoverGluing.glue_eq _ _ _ _ _ _ q (t,z) hz

variable (f : C(Fin 2 → I,X))
  (hf : ∀ q (z : Fin 2 → I), z q.1 = endpoint q.2 →
    D.side q (0,z (other q.1)) = f z)

include hf in
lemma boundary_initial (z : Cube.boundary (Fin 2)) : D.boundary (0,z) = f z := by
  obtain ⟨i,hi|hi⟩ := z.property
  · rw [D.boundary_eq (i,false) 0 z hi]
    exact hf (i,false) z hi
  · rw [D.boundary_eq (i,true) 0 z hi]
    exact hf (i,true) z hi

/-- The complete square prism is extended, not merely its boundary class. -/
def extend : C(I × (Fin 2 → I),X) :=
  CubicalHomotopyExtension.extend f D.boundary (D.boundary_initial f hf)

lemma extend_edge (q : Fin 2 × Bool) (t : I) (z : Fin 2 → I)
    (hz : z q.1 = endpoint q.2) :
    D.extend f hf (t,z) = D.side q (t,z (other q.1)) := by
  have hb : z ∈ Cube.boundary (Fin 2) := by
    refine ⟨q.1,?_⟩
    cases q.2 <;> simp_all [endpoint]
  exact (CubicalHomotopyExtension.extend_side _ _ _ t ⟨z,hb⟩).trans (D.boundary_eq q t ⟨z,hb⟩ hz)

end Data
end HyperbolicObstruction.SquareBoundaryExtension
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TriangleHomotopyExtension
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact homotopy extension on a genuine closed triangle, retaining all
three side tracks and collapsing the fourth square side throughout. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.TriangleHomotopyExtension
open TriangleSquare SquareBoundaryExtension
variable {X : Type*} [TopologicalSpace X]

variable (f : C(Triangle,X)) (D : Data (X := X))
  (hf : ∀ q (z : Fin 2 → I), z q.1 = endpoint q.2 →
    D.side q (0,z (other q.1)) = f (quotient (pairCube z)))
  (ht : ∀ t s, D.side (1,true) (t,s) = D.side (1,true) (t,0))

def square : C(I × (I × I),X) :=
  (D.extend (f.comp (quotient.comp pairCube)) hf).comp
    ((ContinuousMap.id I).prodMap cubePair)

lemma square_edge (q : Fin 2 × Bool) (t : I) (z : I × I)
    (hz : cubePair z q.1 = endpoint q.2) :
    square f D hf (t,z) = D.side q (t,cubePair z (other q.1)) :=
  D.extend_edge _ hf q t (cubePair z) hz

lemma square_top (t s : I) : square f D hf (t,(s,1)) = D.side (1,true) (t,s) :=
  square_edge f D hf (1,true) t (s,1) rfl

include ht in
lemma square_top_const (t s : I) : square f D hf (t,(s,1)) = square f D hf (t,(0,1)) := by
  rw [square_top,square_top,ht]

def extend : C(I × Triangle,X) := TriangleSquare.descend (square f D hf) (square_top_const f D hf ht)

lemma extend_square (t : I) (z : I × I) : extend f D hf ht (t,quotient z) = square f D hf (t,z) :=
  TriangleSquare.descend_quotient _ _ t z

lemma extend_bottom (t s : I) : extend f D hf ht (t,quotient (s,0)) = D.side (1,false) (t,s) := by
  rw [extend_square]
  exact square_edge f D hf (1,false) t (s,0) rfl
lemma extend_left (t s : I) : extend f D hf ht (t,quotient (0,s)) = D.side (0,false) (t,s) := by
  rw [extend_square]
  exact square_edge f D hf (0,false) t (0,s) rfl
lemma extend_right (t s : I) : extend f D hf ht (t,quotient (1,s)) = D.side (0,true) (t,s) := by
  rw [extend_square]
  exact square_edge f D hf (0,true) t (1,s) rfl

end HyperbolicObstruction.TriangleHomotopyExtension
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltageTriangleHomotopy
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend the SAME coherent lifted graph contraction over each actual closed
triangle. Its terminal map is based along all three sides. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
open TriangleSquare SquareBoundaryExtension TriangleHomotopyExtension
variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)
  [SimplyConnectedSpace v.TotalSpace] (z : v.TotalSpace)

omit [Fintype V] [LinearOrder V] [TopologicalSpace G] [DiscreteTopology G]
    [SimplyConnectedSpace v.TotalSpace] in
lemma triangle_voltage {a b c : V} (h : {a,b,c} ∈ K.faces) (g : G) :
    (g*v.value a b)*v.value b c = g*v.value a c := by
  rw [mul_assoc,v.triangle a b c h]

variable {a b c : V} (h : {a,b,c} ∈ K.faces) (g : G)
def triangleSides : SquareBoundaryExtension.Data (X := v.TotalSpace) where
  side q := if q.1 = 0 then
      if q.2 then v.edgeHomotopy z (edge_of_subset K h (by simp) (by simp) : {b,c} ∈ K.faces) (g*v.value a b)
      else v.edgeHomotopy z (edge_of_subset K h (by simp) (by simp) : {a,c} ∈ K.faces) g
    else if q.2 then (v.vertexTrack z c (g*v.value a c)).toContinuousMap.comp ⟨Prod.fst,continuous_fst⟩
      else v.edgeHomotopy z (edge_of_subset K h (by simp) (by simp) : {a,b} ∈ K.faces) g
  corner t i j := by
    cases i <;> cases j <;> dsimp [endpoint]
    · rw [v.edgeHomotopy_left,v.edgeHomotopy_left]
    · rw [v.edgeHomotopy_right]
    · rw [v.edgeHomotopy_left,v.edgeHomotopy_right]
    · rw [v.edgeHomotopy_right,v.triangle_voltage h]

lemma triangleSides_initial (q : Fin 2 × Bool) (w : Fin 2 → I)
    (hw : w q.1 = endpoint q.2) :
    (v.triangleSides z h g).side q (0,w (other q.1)) = v.triangleLift h g (quotient (pairCube w)) := by
  rcases q with ⟨i,j⟩
  fin_cases i <;> cases j <;> dsimp [triangleSides,other,pairCube,endpoint] at hw ⊢
  · change v.edgeHomotopy z _ g (0,w 1) = v.triangleLift h g (quotient (w 0,w 1))
    rw [v.edgeHomotopy_initial,hw,v.triangleLift_left]
  · change v.edgeHomotopy z _ (g*v.value a b) (0,w 1) = v.triangleLift h g (quotient (w 0,w 1))
    rw [v.edgeHomotopy_initial,hw,v.triangleLift_right]
  · change v.edgeHomotopy z _ g (0,w 0) = v.triangleLift h g (quotient (w 0,w 1))
    rw [v.edgeHomotopy_initial,hw,v.triangleLift_bottom]
  · rw [Path.source]
    change v.vertexLift c (g*v.value a c) = v.triangleLift h g (quotient (w 0,w 1))
    rw [hw,quotient_one,←quotient_one (1:I),v.triangleLift_right,Path.target,v.triangle_voltage h]

lemma triangleSides_top (t s : I) :
    (v.triangleSides z h g).side (1,true) (t,s) = (v.triangleSides z h g).side (1,true) (t,0) := rfl

def triangleHomotopy : C(I × Triangle,v.TotalSpace) :=
  TriangleHomotopyExtension.extend (v.triangleLift h g) (v.triangleSides z h g)
    (v.triangleSides_initial z h g) (v.triangleSides_top z h g)

lemma triangleHomotopy_bottom (t s : I) :
    v.triangleHomotopy z h g (t,quotient (s,0)) =
    v.edgeHomotopy z (edge_of_subset K h (by simp) (by simp) : {a,b} ∈ K.faces) g (t,s) :=
  TriangleHomotopyExtension.extend_bottom _ _ _ _ t s
lemma triangleHomotopy_left (t s : I) :
    v.triangleHomotopy z h g (t,quotient (0,s)) =
    v.edgeHomotopy z (edge_of_subset K h (by simp) (by simp) : {a,c} ∈ K.faces) g (t,s) :=
  TriangleHomotopyExtension.extend_left _ _ _ _ t s
lemma triangleHomotopy_right (t s : I) :
    v.triangleHomotopy z h g (t,quotient (1,s)) =
    v.edgeHomotopy z (edge_of_subset K h (by simp) (by simp) : {b,c} ∈ K.faces) (g*v.value a b) (t,s) :=
  TriangleHomotopyExtension.extend_right _ _ _ _ t s

def basedTriangle : C(Triangle,v.TotalSpace) := (v.triangleHomotopy z h g).comp ⟨fun w => (1,w),by fun_prop⟩
lemma basedTriangle_bottom (s : I) : v.basedTriangle z h g (quotient (s,0)) = z := by
  change v.triangleHomotopy z h g (1,_) = _
  rw [v.triangleHomotopy_bottom,v.edgeHomotopy_final]
lemma basedTriangle_left (s : I) : v.basedTriangle z h g (quotient (0,s)) = z := by
  change v.triangleHomotopy z h g (1,_) = _
  rw [v.triangleHomotopy_left,v.edgeHomotopy_final]
lemma basedTriangle_right (s : I) : v.basedTriangle z h g (quotient (1,s)) = z := by
  change v.triangleHomotopy z h g (1,_) = _
  rw [v.triangleHomotopy_right,v.edgeHomotopy_final]

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltageTriangleContraction
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal contracting prism on each lifted triangle once its genuine pi2
obstruction is the coboundary of the constructed directed cochain. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
open TriangleSquare HSpacePathObstruction
variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)
  [SimplyConnectedSpace v.TotalSpace] (z : v.TotalSpace)
  (L : G → V → V → v.LoopClass z)
  (hs : ∀ g a, L g a a = 1)
  (hr : ∀ {a b}, {a,b} ∈ K.faces → ∀ g, L (g*v.value a b) b a = (L g a b)⁻¹)

variable {a b c : V} (h : {a,b,c} ∈ K.faces) (g : G)
abbrev triangleObstruction : v.LoopClass z :=
  BasedTriangleContraction.theta z (v.basedTriangle z h g)
    (v.basedTriangle_bottom z h g) (v.basedTriangle_left z h g) (v.basedTriangle_right z h g)

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonContraction
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A global continuous contraction of the literal polygon voltage cover,
constructed by cochain correction and locally finite closed-cell gluing. -/
noncomputable section

open scoped Topology unitInterval

namespace HyperbolicObstruction.FinitePolygonModel.Data
open FinitePolyhedron FinitePolyhedron.Voltage
variable {V E C G : Type*} [Fintype V] [Fintype E] [Fintype C]
  [DecidableEq V] [DecidableEq E] [DecidableEq C] [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (P : Data V E C) (ρ : E → G)
  (hc : ∀ c, (List.ofFn (fun i => signed ρ (P.side c i))).prod = 1)
  [LinearOrder P.Vertex] [SimplyConnectedSpace (P.voltage ρ hc).TotalSpace]
  (z : (P.voltage ρ hc).TotalSpace)

local instance instCommGroupLoopClassVertexVoltage : CommGroup ((P.voltage ρ hc).LoopClass z) := HSpaceFundamental.commGroup

def obstructionWeight (g : G) (q : P.Position) (j : Fin 3) : Additive ((P.voltage ρ hc).LoopClass z) :=
  Additive.ofMul ((P.voltage ρ hc).triangleObstruction z (P.collar_mem q j) g)

variable (w : G × E → Additive ((P.voltage ρ hc).LoopClass z))

def obstructionCochain (g : G) (a b : P.Vertex) : (P.voltage ρ hc).LoopClass z :=
  Additive.toMul (P.triangleCochain ρ w (P.obstructionWeight ρ hc z) g a b)

lemma obstructionCochain_self (g : G) (a : P.Vertex) : P.obstructionCochain ρ hc z w g a a = 1 := by
  apply Additive.ofMul.injective
  exact P.liftedCochain_self ρ w _ _ _ g a
lemma obstructionCochain_reverse {a b : P.Vertex} (_ : {a,b} ∈ P.complex.faces) (g : G) :
    P.obstructionCochain ρ hc z w (g*(P.voltage ρ hc).value a b) b a =
      (P.obstructionCochain ρ hc z w g a b)⁻¹ := by
  apply Additive.ofMul.injective
  exact P.liftedCochain_reverse ρ w _ _ _ g a b

end HyperbolicObstruction.FinitePolygonModel.Data
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

/-! A literal disk-chain left inverse for the integral cell boundary. The
rooted-edge construction avoids assuming an arbitrary-cycle sphere producer. -/

/-! Subdivision of permutation cycles, with exact orbit-count preservation. -/
namespace PictureSwitch

section
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [Fintype D] [DecidableEq D]

namespace PermInsertion
variable (f : Perm D) (p : D → Prop)

omit [Fintype D] [DecidableEq D] in
lemma collapse_step (x : D ⊕ Subtype p) :
    f.SameCycle (collapse p x) (collapse p (perm f p x)) := by
  rcases x with d|t
  · by_cases h : p d
    · simp only [perm,Equiv.coe_fn_mk,dite_eq_left h,collapse,Sum.elim_inl,Sum.elim_inr,id_eq]
      exact SameCycle.rfl
    · simp only [perm,Equiv.coe_fn_mk,dite_eq_right h,collapse,Sum.elim_inl,id_eq]
      exact SameCycle.rfl.apply_right
  · exact SameCycle.rfl.apply_right

omit [DecidableEq D] in
lemma collapse_sameCycle {x y : D ⊕ Subtype p} (h : (perm f p).SameCycle x y) :
    f.SameCycle (collapse p x) (collapse p y) :=
  (sameCycle_le_of_apply (s := (SameCycle.setoid f).comap (collapse p))
    (collapse_step f p)) h

omit [Fintype D] [DecidableEq D] in
lemma base_step (d : D) : (perm f p).SameCycle (.inl d) (.inl (f d)) := by
  by_cases h : p d
  · have he : perm f p (.inl d) = .inr ⟨d,h⟩ := by simp only [perm,Equiv.coe_fn_mk,dite_eq_left h]
    have he' : perm f p (.inr ⟨d,h⟩) = .inl (f d) := rfl
    have hh := (SameCycle.rfl (f := perm f p) (x := Sum.inl d)).apply_right.apply_right
    rwa [he,he'] at hh
  · have he : perm f p (.inl d) = .inl (f d) := by simp only [perm,Equiv.coe_fn_mk,dite_eq_right h]
    exact he ▸ (SameCycle.rfl (f := perm f p) (x := Sum.inl d)).apply_right

omit [DecidableEq D] in
lemma base_sameCycle {x y : D} (h : f.SameCycle x y) :
    (perm f p).SameCycle (.inl x) (.inl y) :=
  (sameCycle_le_of_apply (s := (SameCycle.setoid (perm f p)).comap Sum.inl)
    (base_step f p)) h

omit [Fintype D] [DecidableEq D] in
lemma collapse_base_cycle (x : D ⊕ Subtype p) :
    (perm f p).SameCycle (.inl (collapse p x)) x := by
  rcases x with d|t
  · exact SameCycle.rfl
  · have he : perm f p (.inl t.val) = .inr t := by simp only [perm,Equiv.coe_fn_mk,dite_eq_left t.property]
    have hh := (SameCycle.rfl (f := perm f p) (x := Sum.inl t.val)).apply_right
    rw [he] at hh
    exact hh

/-- Subdivision gives a genuine equivalence of orbit quotients, including
fixed points and the empty type. -/
def orbitEquiv : Quotient (SameCycle.setoid (perm f p)) ≃ Quotient (SameCycle.setoid f) where
  toFun := Quotient.map (collapse p) (fun _ _ => collapse_sameCycle f p)
  invFun := Quotient.map Sum.inl (fun _ _ => base_sameCycle f p)
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h x => exact Quotient.sound (collapse_base_cycle f p x)
  right_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h x => rfl

end PermInsertion
end

/-! Literal radial triangulation of the free polygon faces of a finite map.
This section concerns genuine permutations; no topological genus assertion is
included in the input. -/

/-! Exact contraction of radial triangle stars. -/
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
end PictureSwitch

/-! Local elementary triangle incidence induces the exact radial contraction. -/

/-! Lifting actual word homotopies to the voltage cover, with the negative
orientation based at the positive lift's initial endpoint. -/
namespace VoltageWords

open HyperbolicObstruction.WordPictures HyperbolicObstruction.PictureSwitch
variable {A G V C : Type*} [Group G]

/-- Encoding the shifted reversal of a voltage cover as a true signed edge.
The negative generator is based at the initial point of its positive reverse. -/
def encode (v : A → G) : G × (A × Bool) ≃ (G × A) × Bool where
  toFun e := liftLetter v e.1 e.2
  invFun e := (if e.2 then e.1.1 else e.1.1 * v e.1.2, (e.1.2,e.2))
  left_inv := by rintro ⟨g,a,b⟩; cases b <;> simp [liftLetter,voltage]
  right_inv := by rintro ⟨⟨g,a⟩,b⟩; cases b <;> simp [liftLetter,voltage]

lemma encode_reverse (v : A → G) (g : G) (e : A × Bool) :
    encode v (g * voltage v e, invLetter e) = invLetter (encode v (g,e)) :=
  liftLetter_inv v g e

def liftedStart (B : PolygonTarget.Boundary C (A × Bool) V) (v : A → G)
    (e : (G × A) × Bool) : G × V :=
  ((encode v).symm e |>.1, B.start ((encode v).symm e |>.2))

lemma liftedStart_encode (B : PolygonTarget.Boundary C (A × Bool) V) (v : A → G)
    (g : G) (e : A × Bool) : liftedStart B v (encode v (g,e)) = (g,B.start e) := by
  simp only [liftedStart,Equiv.symm_apply_apply]

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

section

/-! Reindex the literal finite barycentric carrier onto the frozen challenge's
vertex type `Fin n`. No change of realization or topology is involved. -/

open scoped Topology

namespace FiniteComplex
instance instCompactSpaceCarrier (K : FiniteComplex) : CompactSpace K.Carrier :=
  inferInstanceAs (CompactSpace (FinitePolyhedron.Carrier K.complex))
end FiniteComplex
end

/-! The actual elementary incidence data now defines an actual finite
barycentric polyhedron. This file proves compactness and connectivity only;
no CW-universal-cover comparison is smuggled in as a structure field. -/

/-! Restricting any flat voltage on the actual triangulation to the original
indexed graph. Literal cap triangles prove every original boundary relation. -/

namespace FinitePolygonModel.Data

/-! Literal graph paths and canonical extensions of chosen old-vertex routes. -/

open FinitePolyhedron
variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
  [DecidableEq V] [DecidableEq E] [DecidableEq C]
variable (P : Data V E C)

omit [Fintype V] [Fintype E] [Fintype C] in
lemma graphChain_eval {G : Type*} [Group G] (W : Voltage P.complex G) (e : E × Bool) :
    Voltage.EdgeChain.eval W (P.graphChain e) = P.graphTransport W e := by
  simp only [graphChain,Voltage.EdgeChain.eval_cons,Voltage.EdgeChain.eval_nil,mul_one,graphTransport,mul_assoc]

variable (o : V)
variable (R : P.OldRoutes o)

lemma routes_base (q : P.Position) : P.routes o R (P.base q) = P.baseRoutes o R q := by
  rcases q with ⟨c,i,j⟩
  fin_cases j <;> rfl

abbrev rootedVoltage := RootedPaths.voltage (P.old o) (P.routes o R)

lemma rooted_first (e : E) (b : Bool) :
    (P.rootedVoltage o R).value (P.old (P.start (e,b))) (P.mid e b) = 1 := by
  change RootedPaths.edgeLoop (P.old o) (P.routes o R) _ _ = 1
  rw [RootedPaths.edgeLoop_of_edge _ _ (P.graph_edge_first e b)]
  apply MulOpposite.unop_injective
  exact based_eq_one_of_route (R (P.start (e,b))) (P.edgeClass (P.graph_edge_first e b))

lemma rooted_last (e : E) (b : Bool) :
    (P.rootedVoltage o R).value (P.mid e b) (P.old (P.start (e,b))) = 1 := by
  rw [(P.rootedVoltage o R).reverse (P.graph_edge_first e b),rooted_first,inv_one]

lemma rooted_outer_base (q : P.Position) :
    (P.rootedVoltage o R).value (P.outer q) (P.base q) = 1 := by
  change RootedPaths.edgeLoop (P.old o) (P.routes o R) _ _ = 1
  rw [RootedPaths.edgeLoop_of_edge _ _ (P.outer_base_edge q)]
  apply MulOpposite.unop_injective
  change (P.outerRoutes o R q).trans ((P.edgeClass (P.outer_base_edge q)).trans
    (P.routes o R (P.base q)).symm) = .refl _
  rw [routes_base]
  exact based_eq_one_of_rev_route (P.baseRoutes o R q) (P.edgeClass (P.outer_base_edge q))

lemma rooted_apex_first (c : C) :
    (P.rootedVoltage o R).value (P.apex c) (P.outer (P.firstPosition c)) = 1 := by
  change RootedPaths.edgeLoop (P.old o) (P.routes o R) _ _ = 1
  rw [RootedPaths.edgeLoop_of_edge _ _ (show {P.apex c,P.outer (P.firstPosition c)} ∈ P.complex.faces from P.apex_outer_edge (P.firstPosition c))]
  apply MulOpposite.unop_injective
  exact based_eq_one_of_rev_route (P.outerRoutes o R (P.firstPosition c))
    (P.edgeClass (P.apex_outer_edge (P.firstPosition c)))

lemma rooted_graphTransport (e : E × Bool) :
    P.graphTransport (P.rootedVoltage o R) e = (P.rootedVoltage o R).value (P.mid e.1 e.2) (P.mid e.1 (!e.2)) := by
  rcases e with ⟨e,b⟩
  simp [graphTransport,rooted_first,rooted_last]

end FinitePolygonModel.Data

/-! Genuine continuous fundamental groups are generated by the finite edges. -/

namespace FinitePolyhedron.RootedPaths
variable {V : Type*} [Fintype V] [DecidableEq V] {K : AbstractSimplicialComplex V}
variable (o : V) (R : ∀ a : V, Path.Homotopic.Quotient (vertex K o) (vertex K a))

lemma eq_top_of_edge_mem (hR : R o = .refl _) (H : Subgroup (PiOne (K := K) o))
    (h : ∀ a b, {a,b} ∈ K.faces → (voltage o R).value a b ∈ H) : H = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨p,hp⟩ := Quotient.exists_rep y.unop
  obtain ⟨q,hq⟩ := edgePath_representative K p
  have hm {a b : V} (q : EdgeChain K a b) : Voltage.EdgeChain.eval (voltage o R) q ∈ H := by
    induction q with
    | nil a => exact H.one_mem
    | @cons a b c he q ih => exact H.mul_mem (h a b he) ih
  have hh := hm q
  rw [eval_chain,based_loop o R hR] at hh
  have he : MulOpposite.op q.pathClass = y := by
    apply MulOpposite.unop_injective
    exact (Path.Homotopic.Quotient.eq.mpr hq).symm.trans hp
  rwa [he] at hh

end FinitePolyhedron.RootedPaths

/-! New subdivision, collar and cone edges do not create fundamental-group
generators. This concerns the actual barycentric realization. -/

namespace FinitePolygonModel.Data
open FinitePolyhedron
variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
  [DecidableEq V] [DecidableEq E] [DecidableEq C]
variable (P : Data V E C)

omit [Fintype V] [Fintype E] [Fintype C] [DecidableEq V] [DecidableEq E] [DecidableEq C] in
lemma position_induction (S : P.Position → Prop) (h0 : ∀ c, S (P.firstPosition c))
    (hs : ∀ q, S q → S (P.next q)) (q : P.Position) : S q := by
  rcases q with ⟨c,i,j⟩
  have hi : ∀ k (hk : k < P.size c), S ⟨c,(⟨k,hk⟩,0)⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact h0 c
    | succ k ih =>
      intro hk
      have hk0 : k < P.size c := by omega
      have hh := hs _ (hs _ (hs _ (ih hk0)))
      change S ⟨c,(finRotate _ ⟨k,hk0⟩,0)⟩ at hh
      have hr := finRotate_noWrap (⟨k,hk0⟩ : Fin (P.size c)) hk
      rwa [hr] at hh
  have hh := hi i.val i.isLt
  fin_cases j
  · exact hh
  · exact hs _ hh
  · exact hs _ (hs _ hh)

variable (o : V) (R : P.OldRoutes o)
variable (H : Subgroup (RootedPaths.PiOne (K := P.complex) (P.old o)))
variable (hG : ∀ e, P.graphTransport (P.rootedVoltage o R) e ∈ H)

include hG in
lemma rooted_base_next_mem (q : P.Position) :
    (P.rootedVoltage o R).value (P.base q) (P.base (P.next q)) ∈ H := by
  rw [base_next]
  rcases q with ⟨c,i,j⟩
  fin_cases j
  · change (P.rootedVoltage o R).value (P.old (P.start (P.side c i)))
      (P.mid (P.side c i).1 (P.side c i).2) ∈ H
    rw [rooted_first]
    exact H.one_mem
  · change (P.rootedVoltage o R).value (P.mid (P.side c i).1 (P.side c i).2)
      (P.mid (P.side c i).1 (!(P.side c i).2)) ∈ H
    rw [←rooted_graphTransport]
    exact hG _
  · change (P.rootedVoltage o R).value (P.mid (P.side c i).1 (!(P.side c i).2))
      (P.old (P.start ((P.side c i).1,!(P.side c i).2))) ∈ H
    rw [rooted_last]
    exact H.one_mem

include hG in
lemma rooted_outer_diagonal_mem (q : P.Position) :
    (P.rootedVoltage o R).value (P.outer q) (P.base (P.next q)) ∈ H := by
  have he := P.voltage_on_facet (P.rootedVoltage o R) (.inr (q,0))
    (a := P.outer q) (b := P.base q) (c := P.base (P.next q))
    (by simp [facet,collarFace]) (by simp [facet,collarFace]) (by simp [facet,collarFace])
  rw [rooted_outer_base,one_mul] at he
  rw [←he]
  exact P.rooted_base_next_mem o R H hG q

include hG in
lemma rooted_outer_next_mem (q : P.Position) :
    (P.rootedVoltage o R).value (P.outer q) (P.outer (P.next q)) ∈ H := by
  have he := P.voltage_on_facet (P.rootedVoltage o R) (.inr (q,1))
    (a := P.outer q) (b := P.outer (P.next q)) (c := P.base (P.next q))
    (by simp [facet,collarFace]) (by simp [facet,collarFace]) (by simp [facet,collarFace])
  rw [rooted_outer_base,mul_one] at he
  rw [he]
  exact P.rooted_outer_diagonal_mem o R H hG q

include hG in
lemma rooted_apex_mem (q : P.Position) :
    (P.rootedVoltage o R).value (P.apex q.1) (P.outer q) ∈ H := by
  apply P.position_induction (fun q => (P.rootedVoltage o R).value (P.apex q.1) (P.outer q) ∈ H)
  · intro c
    rw [show (P.firstPosition c).1 = c from rfl,rooted_apex_first]
    exact H.one_mem
  · intro q ih
    have he := P.voltage_on_facet (P.rootedVoltage o R) (.inr (q,2))
      (a := P.apex q.1) (b := P.outer q) (c := P.outer (P.next q))
      (by simp [facet,collarFace]) (by simp [facet,collarFace]) (by simp [facet,collarFace])
    change (P.rootedVoltage o R).value (P.apex q.1) (P.outer (P.next q)) ∈ H
    rw [←he]
    exact H.mul_mem ih (P.rooted_outer_next_mem o R H hG q)

omit [Fintype V] [Fintype E] [Fintype C] in
lemma voltage_facet_mem {G : Type*} [Group G] (W : Voltage P.complex G) (H : Subgroup G)
    (f : P.Facet) {z a b : P.Vertex} (hz : z ∈ P.facet f)
    (hza : W.value z a ∈ H) (hzb : W.value z b ∈ H)
    (ha : a ∈ P.facet f) (hb : b ∈ P.facet f) : W.value a b ∈ H := by
  have ht := P.voltage_on_facet W f hz ha hb
  have he : W.value a b = (W.value z a)⁻¹ * W.value z b := by rw [←ht]; simp
  rw [he]
  exact H.mul_mem (H.inv_mem hza) hzb

include hG in
lemma rooted_facet_mem (f : P.Facet) {a b : P.Vertex} (ha : a ∈ P.facet f) (hb : b ∈ P.facet f) :
    (P.rootedVoltage o R).value a b ∈ H := by
  let W := P.rootedVoltage o R
  have hself (a) : W.value a a ∈ H := by rw [W.self]; exact H.one_mem
  cases f with
  | inl e =>
    rcases e with ⟨e,j⟩
    fin_cases j
    · have hz : ∀ x ∈ P.facet (.inl (e,0)), W.value (P.old (P.start (e,true))) x ∈ H := by
        intro x hx
        simp [facet,graphFace] at hx
        rcases hx with rfl|rfl
        · exact hself _
        · rw [show W = P.rootedVoltage o R from rfl,P.rooted_first]; exact H.one_mem
      exact P.voltage_facet_mem W H (.inl (e,0)) (by simp [facet,graphFace]) (hz a ha) (hz b hb) ha hb
    · have hz : ∀ x ∈ P.facet (.inl (e,1)), W.value (P.mid e true) x ∈ H := by
        intro x hx
        simp [facet,graphFace] at hx
        rcases hx with rfl|rfl
        · exact hself _
        · exact (P.rooted_graphTransport o R (e,true)) ▸ hG (e,true)
      exact P.voltage_facet_mem W H (.inl (e,1)) (by simp [facet,graphFace]) (hz a ha) (hz b hb) ha hb
    · have hz : ∀ x ∈ P.facet (.inl (e,2)), W.value (P.mid e false) x ∈ H := by
        intro x hx
        simp [facet,graphFace] at hx
        rcases hx with rfl|rfl
        · exact hself _
        · rw [show W = P.rootedVoltage o R from rfl,P.rooted_last]; exact H.one_mem
      exact P.voltage_facet_mem W H (.inl (e,2)) (by simp [facet,graphFace]) (hz a ha) (hz b hb) ha hb
  | inr q =>
    rcases q with ⟨q,j⟩
    fin_cases j
    · have hz : ∀ x ∈ P.facet (.inr (q,0)), W.value (P.outer q) x ∈ H := by
        intro x hx
        simp [facet,collarFace] at hx
        rcases hx with rfl|rfl|rfl
        · exact hself _
        · rw [show W = P.rootedVoltage o R from rfl,P.rooted_outer_base]; exact H.one_mem
        · exact P.rooted_outer_diagonal_mem o R H hG q
      exact P.voltage_facet_mem W H (.inr (q,0)) (by simp [facet,collarFace]) (hz a ha) (hz b hb) ha hb
    · have hz : ∀ x ∈ P.facet (.inr (q,1)), W.value (P.outer q) x ∈ H := by
        intro x hx
        simp [facet,collarFace] at hx
        rcases hx with rfl|rfl|rfl
        · exact hself _
        · exact P.rooted_outer_next_mem o R H hG q
        · exact P.rooted_outer_diagonal_mem o R H hG q
      exact P.voltage_facet_mem W H (.inr (q,1)) (by simp [facet,collarFace]) (hz a ha) (hz b hb) ha hb
    · have hz : ∀ x ∈ P.facet (.inr (q,2)), W.value (P.apex q.1) x ∈ H := by
        intro x hx
        simp [facet,collarFace] at hx
        rcases hx with rfl|rfl|rfl
        · exact P.rooted_apex_mem o R H hG q
        · exact P.rooted_apex_mem o R H hG (P.next q)
        · exact hself _
      exact P.voltage_facet_mem W H (.inr (q,2)) (by simp [facet,collarFace]) (hz a ha) (hz b hb) ha hb

include hG in
/-- Only original graph generators are needed for the actual pi1. -/
lemma rooted_group_generated (hR : R o = .refl _) : H = ⊤ := by
  apply RootedPaths.eq_top_of_edge_mem (P.old o) (P.routes o R) hR
  intro a b hab
  rcases hab.2 with hsmall|⟨f,hf⟩
  · have he : a = b := Finset.card_le_one.mp hsmall a (by simp) b (by simp)
    subst b
    rw [(P.rootedVoltage o R).self]
    exact H.one_mem
  · exact P.rooted_facet_mem o R H hG f (hf (by simp)) (hf (by simp))

end FinitePolygonModel.Data

section

/-! Literal monodromy detects rooted edge words. -/

open scoped Topology
open Set
namespace FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

def detect (o : V) : RootedPaths.PiOne (K := K) o →* G where
  toFun p := (v.isQuotientCoveringMap.fundamentalGroupToMulOpposite (v.vertexFiber o 1) p.unop).unop
  map_one' := by
    change (v.isQuotientCoveringMap.fundamentalGroupToMulOpposite (v.vertexFiber o 1) 1).unop = 1
    rw [map_one]
    rfl
  map_mul' p q := by
    change (v.isQuotientCoveringMap.fundamentalGroupToMulOpposite (v.vertexFiber o 1) (q.unop * p.unop)).unop = _
    rw [map_mul,MulOpposite.unop_mul]

lemma detect_eq_iff (o : V) (p : RootedPaths.PiOne (K := K) o) (g : G) :
    v.detect o p = g ↔ g • (v.vertexFiber o 1).val =
      (v.isCoveringMap.monodromy p.unop (v.vertexFiber o 1)).val := by
  change (v.isQuotientCoveringMap.fundamentalGroupToMulOpposite (v.vertexFiber o 1) p.unop).unop = g ↔ _
  rw [←MulOpposite.op_injective.eq_iff]
  simpa only [MulOpposite.op_unop,MulOpposite.unop_op] using
    (v.isQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff
      (e := v.vertexFiber o 1) (γ := p.unop) (g := MulOpposite.op g))

lemma smul_vertexFiber (o : V) (g : G) :
    g • (v.vertexFiber o 1).val = (v.vertexFiber o g).val := by
  apply v.totalSpace_ext
  · rfl
  · change g * 1 = g
    exact mul_one g

lemma detect_chain (o : V) (p : FinitePolyhedron.EdgeChain K o o) :
    v.detect o (MulOpposite.op p.pathClass) = EdgeChain.eval v p := by
  apply (v.detect_eq_iff o _ _).mpr
  change _ = (v.isCoveringMap.monodromy p.pathClass (v.vertexFiber o 1)).val
  rw [EdgeChain.monodromy,one_mul]
  exact v.smul_vertexFiber o _

end FinitePolyhedron.Voltage
end

/-! The literal polygon presentation maps to the actual pi1, and its tree
normalization has no hidden van Kampen hypothesis. -/

namespace FinitePolygonModel.Data
open FinitePolyhedron
variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
  [DecidableEq V] [DecidableEq E] [DecidableEq C]
variable (P : Data V E C)

omit [Fintype V] [Fintype E] [Fintype C] in
lemma graphTransport_voltage {G : Type*} [Group G] (v : E → G)
    (h : ∀ c, (List.ofFn (fun i => signed v (P.side c i))).prod = 1) (e : E × Bool) :
    P.graphTransport (P.voltage v h) e = signed v e := by
  rcases e with ⟨e,b⟩
  cases b <;> simp [graphTransport,voltage,value,graphValue,signed]

variable (o : V) (R : P.OldRoutes o)
lemma rooted_graphChain (e : E × Bool) :
    P.graphTransport (P.rootedVoltage o R) e =
      RootedPaths.based (P.old o) (P.routes o R) (P.graphChain e).pathClass := by
  rw [←graphChain_eval,RootedPaths.eval_chain]

lemma lift_graphTransport (z : List (E × Bool)) :
    FreeGroup.lift (fun e => P.graphTransport (P.rootedVoltage o R) (e,true)) (FreeGroup.mk z) =
      (z.map (P.graphTransport (P.rootedVoltage o R))).prod := by
  rw [FreeGroup.lift_mk]
  congr 1
  apply List.map_congr_left
  intro e he
  conv_rhs => rw [graphTransport_signed]
  rcases e with ⟨e,b⟩
  cases b <;> rfl

lemma polygonRelation_valid (r : FreeGroup E)
    (hr : r ∈ FreeGroup.mk '' Set.range (fun c => List.ofFn (P.side c))) :
    FreeGroup.lift (fun e => P.graphTransport (P.rootedVoltage o R) (e,true)) r = 1 := by
  rcases hr with ⟨z,⟨c,rfl⟩,rfl⟩
  rw [lift_graphTransport,List.map_ofFn]
  exact P.graphTransport_cell (P.rootedVoltage o R) c

def polygonToTopology : P.PolygonGroup →* RootedPaths.PiOne (K := P.complex) (P.old o) :=
  PresentedGroup.toGroup (P.polygonRelation_valid o R)

lemma polygonToTopology_value (e : E × Bool) :
    P.polygonToTopology o R (PresentedGroup.mk _ (FreeGroup.mk [e])) =
      P.graphTransport (P.rootedVoltage o R) e := by
  change FreeGroup.lift (fun e => P.graphTransport (P.rootedVoltage o R) (e,true)) (FreeGroup.mk [e]) = _
  rw [lift_graphTransport]
  simp

end FinitePolygonModel.Data

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
def nodes {a b : K.Vertex} : K.Chain a b → List K.Vertex
  | .nil a => [a]
  | .cons (a := a) _ p => a :: p.nodes

def starts {a b : K.Vertex} : K.Chain a b → List K.Vertex
  | .nil _ => []
  | .cons (a := a) _ p => a :: p.starts

@[simp] lemma nodes_append {a b c : K.Vertex} (p : K.Chain a b) (q : K.Chain b c) :
    (p.append q).nodes = p.starts ++ q.nodes := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [FinitePolyhedron.EdgeChain.append,nodes,starts,ih,List.cons_append]

@[simp] lemma append_nil {a b : K.Vertex} (p : K.Chain a b) : p.append (.nil b) = p := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [FinitePolyhedron.EdgeChain.append,ih]

def single {a b : K.Vertex} (h : K.Edge a b) : K.Chain a b := .cons h (.nil b)

def reverse {a b : K.Vertex} : K.Chain a b → K.Chain b a
  | .nil a => .nil a
  | .cons h p => p.reverse.append (single (by simpa only [Edge,Finset.pair_comm] using h))

end FinitePolyhedron.EdgeChain
end

/-! Rooted path algebra with exact zero-cost spur cancellations. This is a
literal triangular disk calculus, not an appeal to topological equivalence. -/
namespace FinitePolyhedron.EdgeChain
open HyperbolicObstruction.FiniteComplex
variable {K : FiniteComplex}

variable (o : K.Vertex) (R : ∀ a, K.Chain o a)
def based {a b : K.Vertex} (p : K.Chain a b) : K.Chain o o :=
  (R a).append (p.append (R b).reverse)

end FinitePolyhedron.EdgeChain

section

/-! A proved edge-and-triangle presentation of the actual fundamental group
of a finite barycentric realization. The rooted routes are actual edge paths;
no van Kampen theorem or fundamental-group comparison is postulated. -/

attribute [local instance] Classical.propDecidable
open Set
namespace FinitePolyhedron.EdgePresentation
variable {V : Type*} [Fintype V] [DecidableEq V] (K : AbstractSimplicialComplex V)

def freeEval {a b : V} (p : EdgeChain K a b) : FreeGroup (Generator K) := by
  induction p with
  | nil _ => exact 1
  | @cons a b c h q ih => exact FreeGroup.of ⟨(a,b),h⟩ * ih

omit [Fintype V] in
@[simp] lemma freeEval_nil (a : V) : freeEval K (.nil a) = 1 := rfl
omit [Fintype V] in
@[simp] lemma freeEval_cons {a b c : V} (h : {a,b} ∈ K.faces) (q : EdgeChain K b c) :
    freeEval K (.cons h q) = FreeGroup.of ⟨(a,b),h⟩ * freeEval K q := rfl

variable (o : V) (R : ∀ a, EdgeChain K o a)

inductive Relation : FreeGroup (Generator K) → Prop
  | self (a : V) : Relation (FreeGroup.of ⟨(a,a),edge_self K a⟩)
  | triangle {a b c : V} (h : {a,b,c} ∈ K.faces)
      (hab : {a,b} ∈ K.faces) (hbc : {b,c} ∈ K.faces) (hac : {a,c} ∈ K.faces) :
      Relation (FreeGroup.of ⟨(a,b),hab⟩ * FreeGroup.of ⟨(b,c),hbc⟩ * (FreeGroup.of ⟨(a,c),hac⟩)⁻¹)
  | route (a : V) : Relation (freeEval K (R a))

abbrev PresentationGroup :=
  PresentedGroup (show Set (FreeGroup (Generator K)) from Relation K o R)

def gen {a b : V} (h : {a,b} ∈ K.faces) : PresentationGroup K o R :=
  PresentedGroup.of ⟨(a,b),h⟩

end FinitePolyhedron.EdgePresentation
end

/-! Quantitative finite-presentation change, with all word substitutions and
comparison disks constructed. Relator disks are used only after establishing
that the corresponding literal words are null. -/

/-! Literal finite relator words for the proved actual fundamental-group
presentation, including exact rooted route words. -/

/-! Realization of ordinary word disks as literal triangular edge disks over
the frozen finite polyhedron. Free-group folds become actual zero-cost spurs. -/

namespace FiniteComplex

/-! The challenge's literal disk moves preserve every triangular voltage.
This is valid even for the untyped intermediate lists in DiskHomotopy. -/
open FinitePolyhedron
variable (K : FiniteComplex) {G : Type*} [Group G] (v : Voltage K.complex G)

def pathValue : List K.Vertex → G
  | [] => 1
  | [_] => 1
  | a::b::r => v.value a b * pathValue (b::r)

end FiniteComplex

/-! Group-isomorphism transport for geometric actions. -/

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

/-! The finite difference maximum principle required for local geodesic
continuation. Endpoint estimates are literal, with no convergence assumption. -/

/-! Literal equal-time interpolation of finite geodesic polygons. -/
open Set Metric

end HyperbolicObstruction

end

end OAI
end


