-- Prove2me | Definitions.Def_RayBundle_MetricPathGeometry
-- name    : RayBundle_MetricPathGeometry
-- status  : Definition
-- author  : @jawneeboy
-- created : 2026-10-08T18:56:13.621653+00:00
-- url     : https://prove2.me/theorems/240adfd6-f813-4cc3-9cf6-b939de421a7c
-- title:
--   Metric geodesic segments, continuous-path length, and intrinsic extended distance
-- statement:
--   For a metric space $X$ and endpoints $a,b$, a metric segment is an isometric map $[0,d(a,b)]\to X$ with those endpoints. For a continuous path $\gamma:[0,1]\to X$, define its length by metric total variation $\operatorname{Length}(\gamma)=\operatorname{Var}(\gamma)\in[0,\infty]$. The intrinsic extended distance is the infimum of lengths of all continuous paths with specified endpoints. With no such path, the infimum is $\infty$. Path length and intrinsic extended distance are defined for pseudo-emetric spaces.
-- source:
--   Standard unit-edge metric-graph convention: Nicholas Touikan, On geodesic ray bundles in hyperbolic groups, Proceedings of the American Mathematical Society 146 (2018), 4165–4173, Section 2. https://arxiv.org/abs/1706.01979 The present construction and supporting lemmas are proved in the supplied Lean development; these targets are not assigned numbered theorem attributions in that paper.

import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Path

-- Source: RayBundle.Def_Cayley_MetricSegment
namespace RayBundle

/-- An arc-length geodesic segment between two arbitrary metric-space points. -/
structure MetricSegment {X : Type*} [MetricSpace X] (a b : X) where
  map : Set.Icc (0 : ℝ) (dist a b) → X
  isometry : Isometry map
  start : map ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = a
  finish : map ⟨dist a b, ⟨dist_nonneg, le_rfl⟩⟩ = b

end RayBundle

-- Source: RayBundle.Def_Cayley_metricPathLength
namespace RayBundle

open scoped ENNReal

/-- Metric length of a continuous unit-interval path, allowing infinite length. -/
noncomputable def metricPathLength {X : Type*} [PseudoEMetricSpace X] {a b : X}
    (γ : _root_.Path a b) : ℝ≥0∞ := eVariationOn γ Set.univ

end RayBundle

-- Source: RayBundle.Def_Cayley_intrinsicEDist
namespace RayBundle

open scoped ENNReal

/-- Intrinsic distance: the infimum of lengths of all continuous endpoint paths.
If no path exists, the infimum is infinity. -/
noncomputable def intrinsicEDist {X : Type*} [PseudoEMetricSpace X] (a b : X) : ℝ≥0∞ :=
  ⨅ γ : _root_.Path a b, metricPathLength γ

end RayBundle


