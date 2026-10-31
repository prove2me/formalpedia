-- Prove2me | Definitions.Def_PerspEpi_horizonCone
-- name    : PerspEpi_horizonCone
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:31.977217+00:00
-- url     : https://prove2.me/theorems/838532f7-a166-4ec8-836d-0c5d67309c06
-- title:
--   Horizon cone $C^\infty$
-- statement:
--   The **horizon cone** of a set $C$ is
--
--   $$
--   C^\infty = \{ v \mid \exists\, \lambda_k \downarrow 0,\ x_k \in C : \lambda_k x_k \to v \}.
--   $$
--
--   It gives the horizon function through $\operatorname{epi} f^\infty = (\operatorname{epi} f)^\infty$.
--
--   **Formalization Note** "$\lambda_k \downarrow 0$" is encoded as a sequence of positive reals tending to $0$; monotonicity is not required, which gives the same set because every such sequence has a decreasing subsequence.
-- source:
--   Friedlander, Goodwin, Hoheisel, From perspective maps to epigraphical projections, arXiv:2102.06809v1, §1.2 Notation, p.4

import Mathlib

namespace PerspEpi

/-- **Horizon cone.** Friedlander, Goodwin, Hoheisel, *From perspective maps to epigraphical projections*, arXiv:2102.06809v1, §1.2 Notation, p.4:
"the horizon cone is C^∞ := {v ∈ E | ∃{λ_k} ↓ 0, {x_k ∈ C} : λ_k x_k → v}".

**Formalization Note.** "{λ_k} ↓ 0" is encoded as a sequence of positive reals tending to `0`
(`Tendsto t atTop (𝓝[>] 0)`). Monotonicity is not required: every such sequence has a strictly
decreasing subsequence, so the two readings give the same set. -/
def horizonCone {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] (C : Set F) :
    Set F :=
  {v | ∃ (t : ℕ → ℝ) (x : ℕ → F), Filter.Tendsto t Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) ∧
    (∀ k, x k ∈ C) ∧ Filter.Tendsto (fun k => t k • x k) Filter.atTop (nhds v)}

end PerspEpi


