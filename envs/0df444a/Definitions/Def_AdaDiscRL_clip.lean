-- Prove2me | Definitions.Def_AdaDiscRL_clip
-- name    : AdaDiscRL_clip
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:26:00.146644+00:00
-- url     : https://prove2.me/theorems/15c61d9e-831b-4c31-8073-453295815d3b
-- title:
--   Clipping operator $\mathrm{clip}[\mu\mid\nu]$
-- statement:
--   The **clipping operator** is
--   $$
--   \mathrm{clip}[\mu\mid\nu]=\mu\,\mathbb 1[\mu\ge\nu].
--   $$
--   It removes contributions smaller than a gap-dependent threshold in the instance-dependent regret analysis.
--
--   **Formalization Note** p.48 once prints $\mu\mathbb 1[\mu\le\nu]$; Lemma E.1, p.23 and Table 2 use $\mathbb 1[\mu\ge\nu]$, which is taken here.
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Lemma E.1, p.48; p.23; Table 2, p.36

import Mathlib

namespace AdaDiscRL

/-- **Clipping operator** (arXiv:2110.15843v3, p.23 and Lemma E.1, p.48; Table 2, p.36):
`clip[μ | ν] = μ 1[μ ≥ ν]`. (The sentence on p.48 printing `1[μ ≤ ν]` is a slip: Lemma E.1 and
Table 2 use `1[μ ≥ ν]`.) -/
noncomputable def clip (μ ν : ℝ) : ℝ := if ν ≤ μ then μ else 0

end AdaDiscRL


