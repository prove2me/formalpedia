-- Prove2me | Definitions.Def_CarlssonPartition_Approx_Supplement_PartitionOracle
-- name    : CarlssonPartition_Approx_Supplement_PartitionOracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:27:45.580148+00:00
-- url     : https://prove2.me/theorems/c3694780-6921-41c0-8dcd-1ca78cc5838e
-- title:
--   §4 — two planar density measures, line-mass supremum, convex accuracy and exact mass queries
-- statement:
--   Let $R\subseteq\mathbb R^2$ be the known region and let $g_1,g_2$ be measurable nonnegative densities. The two measures are constructed by $\mu_j(Q)=\int_{Q\cap R}g_j(x)\,dx$, with $\mu_j(R)=1$. Densities outside $R$ are irrelevant. For each unit direction $d$, a complete line is parametrized by $p+td$, $t\in\mathbb R$. Define
--   $$
--   K=\sup_{j,p,\|d\|=1}\int_{\mathbb R}\mathbf1_R(p+td)g_j(p+td)\,dt.
--   $$
--   The supremum is first taken in $[0,\infty]$. The input predicate requires it to equal the given finite positive real $K$, rather than silently replacing an unbounded real supremum by zero. The exact integration oracle returns $\mu_j(Q)$ for a requested convex Borel region $Q$ (every region whose mass the procedure of §4.1–4.3 computes, a sliver, half-plane, fan wedge or convex subregion, is convex). Probability normalization makes every reply finite.
--
--   An output is a partition $R=\bigcup_{i=1}^m R_i$ into measurable convex pieces, pairwise disjoint up to area zero, such that
--   $$
--   \left|\mu_j(R_i)-\frac{\mu_j(R)}m\right|\le\varepsilon\quad(i=1,\ldots,m;\ j=1,2).
--   $$
--   An algorithm takes only the public $R,m,K,\varepsilon$; its access to the unknown measures is through the transcript of oracle replies. The cost scale is $K^2m^3\varepsilon^{-2}\log(Km/\varepsilon)$. This is the normalized density setting of §4, not a restriction to uniformly bounded or continuous densities or to polygonal regions.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), §4, p. 15 (PDF 16), §§4.1–4.3, pp. 18–21 (PDF 19–22)

import Mathlib
import Definitions.Def_CarlssonPartition_Equitable_Setting
import Definitions.Def_CarlssonPartition_Approx_Supplement_OraclePrograms

noncomputable section

namespace CarlssonPartition.Approx.Supplement

open MeasureTheory
open scoped ENNReal
open CarlssonPartition.Equitable (Plane)

/-- A query names one of the two measures and a convex Borel subset of the plane. Every
region whose mass the paper's procedure computes (slivers, half-planes, the wedges of a
3-fan, and the convex subregions of the recursion, §4.1–4.3) is convex; arbitrary
non-convex Borel queries would make the oracle stronger and the complexity claim weaker. -/
structure MassQuery where
  measureIndex : Fin 2
  region : Set Plane
  measurable : MeasurableSet region
  convex : Convex ℝ region

/-- The measures are constructed from their densities on R. Nothing requires a
continuous or uniformly bounded density; finite line mass is a separate condition. -/
def partitionMeasure (R : Set Plane) (g : Fin 2 → Plane → ℝ≥0∞) (i : Fin 2) :
    Measure Plane :=
  (volume.restrict R).withDensity (g i)

/-- Exact mass replies. These are extended nonnegative integrals, not Bochner
integrals defaulting to zero. On probability inputs every reply is finite. -/
def massOracle (R : Set Plane) (g : Fin 2 → Plane → ℝ≥0∞) (q : MassQuery) : ℝ≥0∞ :=
  partitionMeasure R g q.measureIndex q.region

/-- The arclength integral on the complete line with base point p and unit direction d.
Restricting the density to R fixes its irrelevant values outside the service region. -/
def lineMass (R : Set Plane) (g : Plane → ℝ≥0∞) (p d : Plane) : ℝ≥0∞ :=
  ∫⁻ t : ℝ, R.indicator g (p + t • d)

/-- The paper's K before conversion to a finite real number. It is a supremum in
ℝ≥0∞: an unbounded family gives infinity rather than a default real value. -/
def lineMassSup (R : Set Plane) (g : Fin 2 → Plane → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (i : Fin 2) (p : Plane) (d : {d : Plane // ‖d‖ = 1}),
    lineMass R (g i) p d.val

/-- The full density domain of §4 with finite line-mass supremum K.
Support is imposed by constructing the restricted measures,
not by an extra continuity or pointwise support hypothesis on the density versions. -/
def PartitionOracleInput (R : Set Plane) (g : Fin 2 → Plane → ℝ≥0∞) (K : ℝ) : Prop :=
  (∀ i, Measurable (g i)) ∧
  (∀ i, partitionMeasure R g i Set.univ = 1) ∧
  lineMassSup R g = ENNReal.ofReal K

/-- Convex partition into all m districts, allowing shared null boundaries as in the
published spatial definition, with both absolute mass errors at most epsilon. -/
def ConvexApproxPartition (R : Set Plane) (g : Fin 2 → Plane → ℝ≥0∞)
    {m : ℕ} (epsilon : ℝ) (Rs : Fin m → Set Plane) : Prop :=
  (∀ i, Convex ℝ (Rs i) ∧ MeasurableSet (Rs i)) ∧
  Pairwise (fun i j => AEDisjoint volume (Rs i) (Rs j)) ∧
  (⋃ i, Rs i) = R ∧
  ∀ (i : Fin m) (j : Fin 2),
    |(partitionMeasure R g j (Rs i)).toReal -
      (partitionMeasure R g j R).toReal / (m : ℝ)| ≤ epsilon

/-- A mass-query algorithm has no density argument. Its public inputs are the region,
number of districts, known line bound and desired accuracy; only replies reveal mass. -/
abbrev PartitionAlgorithm :=
  (R : Set Plane) → (m : ℕ) → (K epsilon : ℝ) →
    QueryProgram MassQuery ℝ≥0∞ (Fin m → Set Plane)

/-- The complete order of the integration-oracle complexity, with natural logarithm.
The theorem uses a small-tolerance range where the logarithm is positive. -/
def partitionQueryScale (K : ℝ) (m : ℕ) (epsilon : ℝ) : ℝ :=
  K ^ 2 * (m : ℝ) ^ 3 / epsilon ^ 2 * Real.log (K * (m : ℝ) / epsilon)

end CarlssonPartition.Approx.Supplement


