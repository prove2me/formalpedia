-- Prove2me | Definitions.Def_SPFacilityGraph_Profile
-- name    : SPFacilityGraph_Profile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:52:38.348787+00:00
-- url     : https://prove2.me/theorems/3b505937-1183-4b8f-8b46-cbe148e63d2c
-- title:
--   Location profiles $\boldsymbol x \in G^n$
-- statement:
--   A **location profile** is a tuple $\boldsymbol x = (x_1, \dots, x_n) \in G^n$ of points of $G$, one ideal location (peak) or report per agent $i \in N = \{1, \dots, n\}$. Writing $(z, \boldsymbol x_{-i})$ for the profile obtained from $\boldsymbol x$ by replacing $x_i$ with $z$, mechanisms are maps on profiles.
--
--   **Formalization Note** Agents are indexed by `Fin n`, i.e. $0, \dots, n-1$.
-- source:
--   Rogowski–Dziubiński, Search and Verification for Strategyproof Facility Location on Metric Graphs, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Section 2.2, p.4

import Mathlib
import Definitions.Def_SPFacilityGraph_MetricGraph_Pt

set_option autoImplicit false

namespace SPFacilityGraph

/-- Location profiles `𝒙 = (x₁, …, xₙ) ∈ Gⁿ` (Rogowski–Dziubiński, *Search and Verification for Strategyproof Facility Location on Metric Graphs*, arXiv:2611.05092 (held version, sha256 4e3d9256…49049), Section 2.2, p.4).

**Formalization Note** Agents are `Fin n` (0-based) instead of `{1, …, n}`. -/
abbrev Profile {k : ℕ} (G : MetricGraph k) (n : ℕ) : Type := Fin n → G.Pt

end SPFacilityGraph


