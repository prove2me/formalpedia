-- Prove2me | Definitions.Def_PlatformCournot_AffineDemand
-- name    : PlatformCournot_AffineDemand
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:20.637195+00:00
-- url     : https://prove2.me/theorems/9b210298-bc10-4ffb-9690-3a64baabe4f7
-- title:
--   Affine inverse demand data $(\alpha_j,\beta_j)_{j\in M}$ with $\alpha_j,\beta_j>0$
-- statement:
--   The markets $M=\{1,\dots,m\}$ of the networked Cournot model have **affine inverse demand**. Market $j$ is described by its intercept $\alpha_j$ (the maximal willingness to pay) and its slope $\beta_j$, and both are strictly positive:
--
--   $$\alpha_j>0,\qquad \beta_j>0\qquad (j\in M).$$
--
--   This data is the demand side of every statement in the mission.
--
--   **Formalization Note** Markets are indexed by `Fin m` (0-based: the paper's market 1 is index 0). The positivity of $(\alpha_j,\beta_j)$, a standing assumption of the paper, is a field of the structure.
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, §2.1 Demand model, p.9

import Mathlib

namespace PlatformCournot

/-- **Affine inverse demand data of the `m` markets.**
Pang, Lin, Fu, Kleeman, Bitar, Wierman, *Transparency and Control in Platforms for Networked
Markets*, arXiv:1903.04574v3, §2.1 "Demand model", p.9: "the price in each market j ∈ M is
determined according to pj(dj) := αj − βjdj … The parameters (αj,βj) are assumed to be strictly
positive for all j ∈ M."

An `AffineDemand m` records the intercept `α j` (maximal willingness to pay) and the slope `β j` of
the inverse demand of every market `j`, both strictly positive.

**Formalization Note** Markets are `Fin m` (0-based: the paper's market 1 is `0`). The standing
positivity of `(αⱼ, βⱼ)` is part of the structure, so every statement of the mission carries it. -/
structure AffineDemand (m : ℕ) where
  /-- The intercept `αⱼ` of market `j`'s inverse demand. -/
  α : Fin m → ℝ
  /-- The slope `βⱼ` of market `j`'s inverse demand. -/
  β : Fin m → ℝ
  α_pos : ∀ j, 0 < α j
  β_pos : ∀ j, 0 < β j

end PlatformCournot


