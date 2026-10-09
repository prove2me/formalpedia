-- Prove2me | Definitions.Def_FastCLO_LowerBound_Rho
-- name    : FastCLO_LowerBound_Rho
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:22:26.868914+00:00
-- url     : https://prove2.me/theorems/ddda4cf6-c945-48f5-85cb-debef92f3d00
-- title:
--   The vertex separation ρ(Z) = inf over z ∈ Z∠ and z′ ∈ conv(Z∠∖{z}) of ‖z − z′‖
-- statement:
--   For a polytope $\mathcal Z$ with extreme points $\mathcal Z^\angle$, the **vertex separation** is
--   $$\rho(\mathcal Z) = \inf_{z\in\mathcal Z^\angle,\ z'\in\mathrm{conv}(\mathcal Z^\angle\setminus\{z\})} \|z - z'\|,$$
--   the smallest Euclidean distance from an extreme point to the convex hull of the remaining extreme points.
--
--   It measures how well separated the candidate decisions are, and it is the scale of the regret lower bounds of the paper (Theorems 3 and 7): a cost vector of norm at most one can make two vertices differ in cost by at most about $\rho(\mathcal Z)$ while keeping one of them strictly optimal.
--
--   **Formalization Note** The infimum is a real `sInf`. The set is bounded below by $0$ and nonempty as soon as $\mathcal Z$ has at least two extreme points. With a single extreme point it is empty and Lean returns $0$; that case never meets the hypotheses of this mission's theorems, where Natarajan shattering forces two distinct extreme points.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, Theorem 3 (definition of ρ(Z)), p. 7

import Mathlib
import Definitions.Def_FastCLO_LowerBound_Model

namespace FastCLO.LowerBound

variable {d : ℕ}

/-- The vertex separation `ρ(Z) = inf_{z∈Z∠, z'∈conv(Z∠∖{z})} ‖z − z'‖` (Theorem 3, Hu, Kallus,
Mao, arXiv:2011.03030v3, p. 7): the smallest distance from an extreme point of `Z` to the convex
hull of the other extreme points.

Formalization Note: a real `sInf`. The set is bounded below by `0`, and it is nonempty as soon as
`Z` has two extreme points; with a single extreme point it is empty and Lean's `sInf ∅ = 0`. That
case never meets the hypotheses of the theorems of this mission (Natarajan shattering of at least
one point needs two distinct extreme points). -/
noncomputable def rho (P : Polytope d) : ℝ :=
  sInf {r | ∃ z ∈ P.ext, ∃ z' ∈ convexHull ℝ (P.ext \ {z}), r = ‖z - z'‖}

end FastCLO.LowerBound


