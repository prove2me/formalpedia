-- Prove2me | Definitions.Def_CKSBondiPenrose_002
-- name    : CKSBondiPenrose_002
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:03.337509+00:00
-- url     : https://prove2.me/theorems/a941c76f-b75d-4204-93cf-c0d6047487c4
-- statement:
--   For a smooth three-dimensional manifold N with boundary, a Riemannian metric q, and a bilinear tensor k, these definitions describe null expansions and the hypotheses for a Bondi–Penrose statement. In a surface parametrization f, the second fundamental form is minus the q-pairing of the normal with the covariant second derivative of f; its trace in the Gram–Schmidt orthonormal tangent frame is the mean curvature H, while tracing k in the same frame gives trΣ k. BoundaryGeometry supplies a unit normal orthogonal to the boundary, with positive coordinate 0 in the half-space tangent model, local smooth coefficient charts representing q and k, and smoothness of the coordinate normal. Its boundary expansion is θ₊ = H + trΣ k; MarginalBoundary is the proposition that such boundary geometry exists with θ₊ identically zero. A coefficient atlas chooses such a coefficient chart at every point. An InteriorSurface is a smooth embedded immersion of a smooth two-dimensional manifold into the interior of N, equipped with a smooth unit orthogonal normal; its local parametrizations define H, trΣ k, and θ± = H ± trΣ k. It SeparatesAway from a specified coordinate end if its image is the frontier of a set B equal to the closure of its nonempty interior and contained outside the end or within some bounded coordinate radius larger than the end radius. No condition that B contain the original boundary is imposed. ComponentwiseApparent means that on each connected component either θ₊ vanishes everywhere or θ₋ vanishes everywhere, with the choice allowed to vary between components. NoAdditionalHorizons excludes every such separating, componentwise apparent surface whose parameter manifold is nonempty, compact, Hausdorff, and second countable. For source end data d with mass aspect M, the Bondi energy and momentum are (E,P) = (16π)⁻¹∫S² M(n)(1,n) dω, and bondiMass(d) = √(E² − ‖P‖²). MainHypotheses, on a connected Hausdorff second-countable N, assumes smooth symmetric K, orientability, a compact nonempty connected boundary, completeness of the Riemannian distance, the local dominant energy condition μ ≥ |J| with μ = (R + (tr K)² − |K|²)/2 and J = div K − d(tr K), E > ‖P‖, a marginal boundary, positive minimum enclosing area, and NoAdditionalHorizons for d's end and the chosen atlas. The minimum enclosing area is the infimum of boundary areas of smooth closed connected exterior domains containing everything outside some compact set. Finally, for m > 0, SchwarzschildExample(m) is a defined existence proposition: the specified Schwarzschild metric and tensor admit source end data and an atlas satisfying MainHypotheses, their prescribed spacetime graph is smooth through the horizon with the required induced metric, second form, and future unit normal, their Bondi mass is m, and their minimum enclosing area is 16πm², giving bondiMass = √(minimumEnclosingArea/(16π)). These structures record assumptions and definitions, rather than proving the existence proposition.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CKSBondiPenrose.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CKSBondiPenrose.lean; bytes 179638..193107
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_CKSBondiPenrose

noncomputable section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6

namespace OAI.CKSSourceExterior

open Set Manifold Bundle Filter CKSLorentz CKSMetricGluing CKSSpatialManifold CKSGeometricCuts

open CKSADM (Symbol)

open scoped ContDiff Topology

variable {N : Type u_1} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
  [T2Space N] [SecondCountableTopology N] [ConnectedSpace N]

attribute [local instance] manifold_regular



end OAI.CKSSourceExterior
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSMain
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
attribute [local instance] manifold_regular


def secondForm (q : OAI.CKSLorentz.SpatialTensor) (f : OAI.CKSBoundarySurface.E2 → OAI.CKSBoundarySurface.E3) (y : OAI.CKSBoundarySurface.E2) (ν : OAI.CKSBoundarySurface.E3)
    (a b : OAI.CKSBoundarySurface.E2) : ℝ :=
  -(q (f y) ν (fderiv ℝ (fun z => fderiv ℝ f z b) y a) +
    OAI.CKSSchwarzschild.christoffelPair q (f y) (fderiv ℝ f y a) (fderiv ℝ f y b) ν)

def meanCurvature (q : OAI.CKSLorentz.SpatialTensor) (f : OAI.CKSBoundarySurface.E2 → OAI.CKSBoundarySurface.E3) (y : OAI.CKSBoundarySurface.E2) (ν : OAI.CKSBoundarySurface.E3) : ℝ :=
  let a := OAI.CKSSchwarzschild.firstFrame (q (f y)) (fderiv ℝ f y)
  let b := OAI.CKSSchwarzschild.secondFrame (q (f y)) (fderiv ℝ f y)
  OAI.CKSMain.secondForm q f y ν a a + OAI.CKSMain.secondForm q f y ν b b

def tangentialTrace (q k : OAI.CKSLorentz.SpatialTensor) (f : OAI.CKSBoundarySurface.E2 → OAI.CKSBoundarySurface.E3) (y : OAI.CKSBoundarySurface.E2) : ℝ :=
  let a := fderiv ℝ f y (OAI.CKSSchwarzschild.firstFrame (q (f y)) (fderiv ℝ f y))
  let b := fderiv ℝ f y (OAI.CKSSchwarzschild.secondFrame (q (f y)) (fderiv ℝ f y))
  k (f y) a a + k (f y) b b

end OAI.CKSMain
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSMain
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
attribute [local instance] manifold_regular
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]

structure BoundaryGeometry (q : OAI.CKSMetricGluing.SmoothMetric OAI.CKSBoundarySurface.I3 (M := N)) (k : OAI.CKSMetricGluing.InnerField OAI.CKSBoundarySurface.I3 (M := N)) where
  normal : ∀ p : OAI.CKSBoundarySurface.Boundary N, TangentSpace OAI.CKSBoundarySurface.I3 p.val
  unit : ∀ p, q.inner p.val (normal p) (normal p) = 1
  orthogonal : ∀ p a, q.inner p.val (normal p)
    (mfderiv OAI.CKSBoundarySurface.I2 OAI.CKSBoundarySurface.I3 (Subtype.val : OAI.CKSBoundarySurface.Boundary N → N) p a) = 0
  inward : ∀ p, 0 < (show OAI.CKSBoundarySurface.E3 from normal p) 0
  chart : ∀ p : OAI.CKSBoundarySurface.Boundary N, OAI.CKSIntrinsicConstraints.ConstraintChart q.inner k p.val
  normal_smooth : ∀ p, ContMDiffAt OAI.CKSBoundarySurface.I2 𝓘(ℝ,OAI.CKSBoundarySurface.E3) ∞
    (fun z : OAI.CKSBoundarySurface.Boundary N => mfderiv OAI.CKSBoundarySurface.I3 𝓘(ℝ,OAI.CKSBoundarySurface.E3) (chart p).coordinate z.val (normal z)) p

def BoundaryGeometry.parameter {q : OAI.CKSMetricGluing.SmoothMetric OAI.CKSBoundarySurface.I3 (M := N)} {k : OAI.CKSMetricGluing.InnerField OAI.CKSBoundarySurface.I3 (M := N)}
    (B : OAI.CKSMain.BoundaryGeometry q k) (p : OAI.CKSBoundarySurface.Boundary N) : OAI.CKSBoundarySurface.E2 → OAI.CKSBoundarySurface.E3 :=
  (B.chart p).coordinate ∘ (Subtype.val : OAI.CKSBoundarySurface.Boundary N → N) ∘ (extChartAt OAI.CKSBoundarySurface.I2 p).symm

def BoundaryGeometry.thetaPlus {q : OAI.CKSMetricGluing.SmoothMetric OAI.CKSBoundarySurface.I3 (M := N)} {k : OAI.CKSMetricGluing.InnerField OAI.CKSBoundarySurface.I3 (M := N)}
    (B : OAI.CKSMain.BoundaryGeometry q k) (p : OAI.CKSBoundarySurface.Boundary N) : ℝ :=
  let c := B.chart p
  let f := B.parameter p
  let y := (extChartAt OAI.CKSBoundarySurface.I2 p) p
  let ν := mfderiv OAI.CKSBoundarySurface.I3 𝓘(ℝ,OAI.CKSBoundarySurface.E3) c.coordinate p.val (B.normal p)
  OAI.CKSMain.meanCurvature c.metric f y ν + OAI.CKSMain.tangentialTrace c.metric c.tensor f y

def MarginalBoundary (q : OAI.CKSMetricGluing.SmoothMetric OAI.CKSBoundarySurface.I3 (M := N)) (k : OAI.CKSMetricGluing.InnerField OAI.CKSBoundarySurface.I3 (M := N)) : Prop :=
  ∃ B : OAI.CKSMain.BoundaryGeometry q k, ∀ p, B.thetaPlus p = 0

def bondiMass {g : OAI.CKSMetricGluing.SmoothMetric OAI.CKSBoundarySurface.I3 (M := N)} {K : OAI.CKSMetricGluing.InnerField OAI.CKSBoundarySurface.I3 (M := N)}
    (d : OAI.CKSSourceExterior.CKSData g K) : ℝ :=
  Real.sqrt ((OAI.CKSLorentz.bondiCharge d.massAspect).1^2 - ‖(OAI.CKSLorentz.bondiCharge d.massAspect).2‖^2)

end OAI.CKSMain
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSMain
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology InnerProductSpace
open CKSSchwarzschild
attribute [local instance] manifold_regular
attribute [local instance] CKSIntrinsicConstraints.halfSpaceDimension_neZero
attribute [local instance] CKSSpatialManifold.real_id_isometric CKSLorentz.real_smulCommClass CKSLorentz.spatialDual_smulCommClass


local instance atlas_manifold_one {N : Type u_1} [TopologicalSpace N] [ChartedSpace OAI.CKSBoundarySurface.H3 N]
    [IsManifold OAI.CKSBoundarySurface.I3 ∞ N] : IsManifold OAI.CKSBoundarySurface.I3 1 N := inferInstance

local instance atlas_tangent_vectorBundle {N : Type u_1} [TopologicalSpace N] [ChartedSpace OAI.CKSBoundarySurface.H3 N]
    [IsManifold OAI.CKSBoundarySurface.I3 ∞ N] :
    letI := OAI.CKSMain.atlas_manifold_one (N := N)
    VectorBundle ℝ OAI.CKSBoundarySurface.E3 (fun x : N => TangentSpace OAI.CKSBoundarySurface.I3 x) := by
  infer_instance

abbrev CoefficientAtlas {N : Type u_1} [TopologicalSpace N] [ChartedSpace OAI.CKSBoundarySurface.H3 N]
    [IsManifold OAI.CKSBoundarySurface.I3 ∞ N] (q : OAI.CKSMetricGluing.SmoothMetric OAI.CKSBoundarySurface.I3 (M := N)) (k : OAI.CKSMetricGluing.InnerField OAI.CKSBoundarySurface.I3 (M := N)) :=
  letI := OAI.CKSMain.atlas_manifold_one (N := N)
  letI := OAI.CKSMain.atlas_tangent_vectorBundle (N := N)
  let metric : ContMDiffRiemannianMetric OAI.CKSBoundarySurface.I3 ∞ OAI.CKSBoundarySurface.E3 (fun x : N => TangentSpace OAI.CKSBoundarySurface.I3 x) := q
  ∀ x : N, OAI.CKSIntrinsicConstraints.ConstraintChart metric.inner k x

end OAI.CKSMain
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSMain
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
attribute [local instance] manifold_regular
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]

structure InteriorSurface (q : OAI.CKSMetricGluing.SmoothMetric OAI.CKSBoundarySurface.I3 (M := N)) (k : OAI.CKSMetricGluing.InnerField OAI.CKSBoundarySurface.I3 (M := N))
    (A : OAI.CKSMain.CoefficientAtlas q k) (T : Type v) [TopologicalSpace T] [ChartedSpace OAI.CKSBoundarySurface.E2 T]
    [IsManifold OAI.CKSBoundarySurface.I2 ∞ T] where
  map : T → N
  smooth : ContMDiff OAI.CKSBoundarySurface.I2 OAI.CKSBoundarySurface.I3 ∞ map
  embedding : Topology.IsEmbedding map
  immersion : ∀ p, Function.Injective (mfderiv OAI.CKSBoundarySurface.I2 OAI.CKSBoundarySurface.I3 map p)
  interior : ∀ p, map p ∈ OAI.CKSBoundarySurface.I3.interior N
  normal : ∀ p, TangentSpace OAI.CKSBoundarySurface.I3 (map p)
  normal_unit : ∀ p, q.inner (map p) (normal p) (normal p) = 1
  normal_orthogonal : ∀ p a, q.inner (map p) (normal p) (mfderiv OAI.CKSBoundarySurface.I2 OAI.CKSBoundarySurface.I3 map p a) = 0
  normal_smooth : ∀ p, ContMDiffAt OAI.CKSBoundarySurface.I2 𝓘(ℝ,OAI.CKSBoundarySurface.E3) ∞
    (fun t => mfderiv OAI.CKSBoundarySurface.I3 𝓘(ℝ,OAI.CKSBoundarySurface.E3) (A (map p)).coordinate (map t) (normal t)) p

end OAI.CKSMain
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSMain.InteriorSurface
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
attribute [local instance] manifold_regular
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
variable {q : SmoothMetric I3 (M := N)} {k : InnerField I3 (M := N)}
  {A : CoefficientAtlas q k} {T : Type v} [TopologicalSpace T] [ChartedSpace E2 T]
  [IsManifold I2 ∞ T] (D : InteriorSurface q k A T)

def parameter (p : T) : OAI.CKSBoundarySurface.E2 → OAI.CKSBoundarySurface.E3 :=
  (A (D.map p)).coordinate ∘ D.map ∘ (extChartAt OAI.CKSBoundarySurface.I2 p).symm

def mean (p : T) : ℝ :=
  let c := A (D.map p)
  OAI.CKSMain.meanCurvature c.metric (D.parameter p) ((extChartAt OAI.CKSBoundarySurface.I2 p) p)
    (mfderiv OAI.CKSBoundarySurface.I3 𝓘(ℝ,OAI.CKSBoundarySurface.E3) c.coordinate (D.map p) (D.normal p))

def trace (p : T) : ℝ :=
  let c := A (D.map p)
  OAI.CKSMain.tangentialTrace c.metric c.tensor (D.parameter p) ((extChartAt OAI.CKSBoundarySurface.I2 p) p)

def thetaPlus (p : T) : ℝ := D.mean p + D.trace p

def thetaMinus (p : T) : ℝ := D.mean p - D.trace p

def SeparatesAway (c : OAI.CKSSourceExterior.CoordinateEnd (N := N)) : Prop :=
  ∃ B : Set N, B = closure (_root_.interior B) ∧ (_root_.interior B).Nonempty ∧
    frontier B = range D.map ∧
    ∃ r : ℝ, c.radius < r ∧ B ⊆ {x | x ∉ c.domain ∨ ‖c.coordinate x‖ ≤ r}

def ComponentwiseApparent : Prop :=
  ∀ p : T, (∀ z ∈ connectedComponent p, D.thetaPlus z = 0) ∨
    (∀ z ∈ connectedComponent p, D.thetaMinus z = 0)

end OAI.CKSMain.InteriorSurface
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSMain
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
attribute [local instance] manifold_regular
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]

def NoAdditionalHorizons (q : OAI.CKSMetricGluing.SmoothMetric OAI.CKSBoundarySurface.I3 (M := N)) (k : OAI.CKSMetricGluing.InnerField OAI.CKSBoundarySurface.I3 (M := N))
    (c : OAI.CKSSourceExterior.CoordinateEnd (N := N)) (A : OAI.CKSMain.CoefficientAtlas q k) : Prop :=
  ∀ (T : Type v) [TopologicalSpace T] [ChartedSpace OAI.CKSBoundarySurface.E2 T] [IsManifold OAI.CKSBoundarySurface.I2 ∞ T]
    [T2Space T] [SecondCountableTopology T] [CompactSpace T] [Nonempty T]
    (D : OAI.CKSMain.InteriorSurface q k A T), D.SeparatesAway c → ¬ D.ComponentwiseApparent

structure MainHypotheses [T2Space N] [SecondCountableTopology N] [ConnectedSpace N]
    (g : OAI.CKSMetricGluing.SmoothMetric OAI.CKSBoundarySurface.I3 (M := N)) (K : OAI.CKSMetricGluing.InnerField OAI.CKSBoundarySurface.I3 (M := N))
    (d : OAI.CKSSourceExterior.CKSData g K) (A : OAI.CKSMain.CoefficientAtlas g K) : Prop where
  smooth_tensor : ContMDiff OAI.CKSBoundarySurface.I3 (OAI.CKSBoundarySurface.I3.prod 𝓘(ℝ,OAI.CKSLorentz.SpatialBilinear)) ∞ (OAI.CKSMetricGluing.innerSection OAI.CKSBoundarySurface.I3 K)
  symmetric_tensor : ∀ x v w, K x v w = K x w v
  orientable : OAI.CKSSourceExterior.Orientable (N := N)
  boundary_compact : IsCompact (OAI.CKSBoundarySurface.I3.boundary N)
  boundary_nonempty : (OAI.CKSBoundarySurface.I3.boundary N).Nonempty
  complete : OAI.CKSReplacementCompleteness.IsComplete OAI.CKSBoundarySurface.I3 g.toContinuousRiemannianMetric
  dec : OAI.CKSSpatialManifold.PhysicalDEC OAI.CKSBoundarySurface.I3 g.inner K
  timelike : ‖(OAI.CKSLorentz.bondiCharge d.massAspect).2‖ < (OAI.CKSLorentz.bondiCharge d.massAspect).1
  boundary_connected : ConnectedSpace (OAI.CKSBoundarySurface.Boundary N)
  boundary_marginal : OAI.CKSMain.MarginalBoundary g K
  positive_area : 0 < OAI.CKSSourceExterior.minimumEnclosingArea g
  no_horizons : OAI.CKSMain.NoAdditionalHorizons.{u,v} g K d.chart A

end OAI.CKSMain
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSMain
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
attribute [local instance] manifold_regular
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]
attribute [local instance] sixteen_atLeastTwo


def SchwarzschildExample (m : ℝ) (_hm : 0 < m) : Prop :=
  ∃ (g : OAI.CKSMetricGluing.SmoothMetric OAI.CKSBoundarySurface.I3 (M := OAI.CKSSchwarzschild.Exterior))
    (d : OAI.CKSSourceExterior.CKSData g (OAI.CKSSchwarzschild.tensorInner m))
    (A : OAI.CKSMain.CoefficientAtlas g (OAI.CKSSchwarzschild.tensorInner m)),
    (∀ p, g.inner p = OAI.CKSSchwarzschild.metricInner m p) ∧
    OAI.CKSMain.MainHypotheses.{0,v} g (OAI.CKSSchwarzschild.tensorInner m) d A ∧
    OAI.CKSSchwarzschild.HorizonRegularGraph m ∧
    OAI.CKSMain.bondiMass d = m ∧
    OAI.CKSSourceExterior.minimumEnclosingArea g = 16*Real.pi*m^2 ∧
    OAI.CKSMain.bondiMass d = Real.sqrt (OAI.CKSSourceExterior.minimumEnclosingArea g / (16*Real.pi))

end OAI.CKSMain
end

noncomputable section
universe u v w u_1 u_2 u_3 u_4 u_5 u_6
namespace OAI.CKSMain
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
attribute [local instance] manifold_regular
open CKSSchwarzschild



end OAI.CKSMain
end


