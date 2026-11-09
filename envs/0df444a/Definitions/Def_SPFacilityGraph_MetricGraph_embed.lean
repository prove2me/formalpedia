-- Prove2me | Definitions.Def_SPFacilityGraph_MetricGraph_embed
-- name    : SPFacilityGraph_MetricGraph_embed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:58:27.666843+00:00
-- url     : https://prove2.me/theorems/4650cb22-5756-49a1-9cc3-873f7c9cb3a8
-- title:
--   A profile as a point of $(\mathbb R^k)^n$
-- statement:
--   Each profile $\boldsymbol x \in G^n$ is a point $(x_1, \dots, x_n)$ of $(\mathbb R^k)^n$. This embedding exhibits $G^n$ as a polyhedron in $(\mathbb R^k)^n$, the domain that triangulations and polytope covers of the profile space live in.
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Section 3.2, p.7 ("G and its finite Cartesian powers are polyhedra")

import Mathlib
import Definitions.Def_SPFacilityGraph_Profile

set_option autoImplicit false

namespace SPFacilityGraph

/-- A profile `𝒙 ∈ Gⁿ` viewed as a point of `(ℝ^k)ⁿ`, the ambient space in which `Gⁿ` is a
polyhedron (Rogowski–Dziubiński, *Search and Verification for Strategyproof Facility Location on Metric Graphs*, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Section 3.2, p.7: "G and its finite Cartesian powers are polyhedra"). -/
def MetricGraph.embed {k n : ℕ} (G : MetricGraph k) (x : Profile G n) :
    Fin n → EuclideanSpace ℝ (Fin k) :=
  fun j => (x j : EuclideanSpace ℝ (Fin k))

end SPFacilityGraph


