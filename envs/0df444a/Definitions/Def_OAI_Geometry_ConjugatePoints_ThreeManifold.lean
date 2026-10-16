-- Prove2me | Definitions.Def_OAI_Geometry_ConjugatePoints_ThreeManifold
-- name    : OAI_Geometry_ConjugatePoints_ThreeManifold
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:05:10.409834+00:00
-- url     : https://prove2.me/theorems/a816bb6f-4d31-40f7-b462-3660a8baa87e
-- title:
--   CN midpoints and deck isometries for the universal-cover distance of a nonpositively curved metric
-- statement:
--   Let $M$ be a compact Hausdorff $C^\infty$ manifold modelled on $\mathbb{R}^3$, $g$ a smooth Riemannian metric on $M$ with nonpositive sectional curvature (in the chartwise sense of the main theorem: $g(R(u,v)v,u)\le0$ for all coordinate vectors $u,v$ at every point of every chart), and $p\in M$. Let $\exp_p:\mathbb{R}^3\to M$ be the exponential map at $p$, where $\mathbb{R}^3$ is the tangent space at $p$ expressed in the chart at $p$ and $\exp_p(v)$ is the time-one value of the geodesic with initial velocity $v$. Let $D_p$ be the Riemannian distance on $\mathbb{R}^3$ of the pulled-back metric $\exp_p^{*}g$; this makes $\mathbb{R}^3$ a metric space (the universal-cover distance).
--
--   1. **CN inequality.** For all $a,b\in\mathbb{R}^3$ there is $m\in\mathbb{R}^3$ such that for every $z\in\mathbb{R}^3$
--   $$
--   D_p(m,z)^2\le\frac{D_p(a,z)^2+D_p(b,z)^2}{2}-\frac{D_p(a,b)^2}{4}.
--   $$
--
--   2. **CN midpoint structure.** A CN midpoint structure on a metric space $(Y,d)$ is a map $\operatorname{mid}:Y\times Y\to Y$ such that $d(\operatorname{mid}(x,y),z)^2\le\frac{d(x,z)^2+d(y,z)^2}{2}-\frac{d(x,y)^2}{4}$ for all $x,y,z$. The universal CN structure on $(\mathbb{R}^3,D_p)$ chooses, for each pair $(a,b)$, a point $m$ given by item 1.
--
--   3. **Deck isometries.** The deck group of $\exp_p$ is the group of homeomorphisms $d$ of $\mathbb{R}^3$ with $\exp_p\circ d=\exp_p$. The map sending a deck transformation $d$ to $d$ regarded as an isometry of $(\mathbb{R}^3,D_p)$ is a group homomorphism from the deck group to the isometry group of $(\mathbb{R}^3,D_p)$.
--
--   4. **Base-point transport.** For a topological space $Y$ and points $x=y$, the canonical group isomorphism $\pi_1(Y,x)\cong\pi_1(Y,y)$ (the identity after substituting the equality).
--
--   The CN (Bruhat–Tits) inequality says that $(\mathbb{R}^3,D_p)$ behaves like a nonpositively curved metric space, and the deck group acts on it by isometries. These are the ingredients of the obstruction showing that the fundamental group of the glued manifold cannot act in this way, so that it admits no metric of nonpositive sectional curvature.
--
--   **Formalization Note** The distance is `universalMetric g hn p`, a `MetricSpace` structure on `E3 = Fin 3 → ℝ` passed explicitly (hence the `@`-notation), so the statements refer to this distance rather than the Euclidean one. Item 1 (`universalMetric_exists_CN`) is a theorem stored in this definition file; the choice in `universalCN` is made with `Classical.choose`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/ThreeManifold.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/ThreeManifold.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ConjugatePoints mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning
import Definitions.Def_OAI_Geometry_ConjugatePoints_Index
import Definitions.Def_OAI_Geometry_ConjugatePoints_CompactMetric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Curvature
import Definitions.Def_OAI_Geometry_ConjugatePoints_Geodesics
import Definitions.Def_OAI_Geometry_ConjugatePoints_Continuation
import Definitions.Def_OAI_Geometry_ConjugatePoints_Distance
import Definitions.Def_OAI_Geometry_ConjugatePoints_Convexity
import Definitions.Def_OAI_Geometry_ConjugatePoints_FundamentalGroup
import Definitions.Def_OAI_Geometry_ConjugatePoints_Passages
import Definitions.Def_OAI_Geometry_ConjugatePoints_NoConjugatePoints

namespace OAI

noncomputable section

/-!
# The universal-cover shear obstruction and the three-manifold existence theorem.
-/

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff UpperHalfPlane
namespace ThreeManifold.CompactMetric
open GluedConstruction HyperbolicCore LoopTopology RiemannianCoordinates
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

theorem universalMetric_exists_CN (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (a b : E3) :
    let D := @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist
    ∃ m : E3, ∀ z, D m z ^2 ≤ (D a z ^2 + D b z ^2)/2 - D a b ^2/4 := by
  let q := exponential g p a
  have hbase : exponential g p a = exponential g q 0 := (exponential_zero g q).symm
  obtain ⟨e,he0,he,hc,hci,hi⟩ := exists_exponential_coordinates g hn a 0 hbase
  let D := @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist
  let Q := @dist E3 (universalMetric g hn q).toPseudoMetricSpace.toDist
  have hid (x y : E3) : Q (e x) (e y) = D x y :=
    @Isometry.dist_eq E3 E3 (universalMetric g hn p).toPseudoMetricSpace
      (universalMetric g hn q).toPseudoMetricSpace e hi x y
  refine ⟨e.symm ((1/2:ℝ) • e b),fun z => ?_⟩
  have hh := universalMetric_radial_CN g hn q (e b) (e z)
  change Q ((1/2:ℝ) • e b) (e z) ^2 ≤
    (Q 0 (e z) ^2 + Q (e b) (e z) ^2)/2 - Q 0 (e b) ^2/4 at hh
  rw [← he0,hid,hid,hid] at hh
  change D (e.symm ((1/2:ℝ) • e b)) z ^2 ≤ _
  rw [← hid,e.apply_symm_apply]
  exact hh

def universalCN (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g) (p : M) :
    @NonpositiveMetric.CNMidpoint E3 (universalMetric g hn p) := by
  refine @NonpositiveMetric.CNMidpoint.mk E3 (universalMetric g hn p)
    (fun a b => (universalMetric_exists_CN g hn p a b).choose) ?_
  intro a b z
  exact (universalMetric_exists_CN g hn p a b).choose_spec z
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold MeasureTheory
open scoped ContDiff ENNReal
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

def npcDeckIsometry (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g) (p : M) :
    UniversalDeck.group (exponential g p) →*
      @IsometryEquiv E3 E3 (universalMetric g hn p).toPseudoEMetricSpace
        (universalMetric g hn p).toPseudoEMetricSpace where
  toFun d := @IsometryEquiv.mk E3 E3 (universalMetric g hn p).toPseudoEMetricSpace
    (universalMetric g hn p).toPseudoEMetricSpace d.val (universalMetric_deck_isometry g hn p d)
  map_one' := by apply DFunLike.ext; intro x; rfl
  map_mul' _ _ := by apply DFunLike.ext; intro x; rfl

end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.LoopTopology
variable {X : Type} [TopologicalSpace X]
def groupBasepointEq {x y : X} (h : x = y) : FundamentalGroup X x ≃* FundamentalGroup X y := by
  subst y
  exact MulEquiv.refl _
end ThreeManifold.LoopTopology
namespace ThreeManifold.CompactMetric
open GluedConstruction RiemannianCoordinates LoopTopology

end ThreeManifold.CompactMetric
end

namespace ThreeManifold
open Set GluedConstruction CompactMetric

end ThreeManifold

end

end OAI


