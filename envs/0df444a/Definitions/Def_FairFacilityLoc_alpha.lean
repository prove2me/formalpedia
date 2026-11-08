-- Prove2me | Definitions.Def_FairFacilityLoc_alpha
-- name    : FairFacilityLoc_alpha
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:15.603876+00:00
-- url     : https://prove2.me/theorems/56f6ae58-1783-434a-90ef-474aeae6007c
-- title:
--   The constant $\alpha_d$, (1.2)
-- statement:
--   $$\alpha_d=\begin{cases}1+\sqrt d,&1\le d\le3,\\3,&d\ge4.\end{cases}$$
--
--   This is the ratio of Theorem 1.1.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), (1.2), p.2 (PDF p.4)

import Mathlib

namespace FairFacilityLoc

/-- The **constant** `α_d`, (1.2), p.2, PDF p.4: `α_d = 1 + √d` for `1 ≤ d ≤ 3` and `α_d = 3` for `d ≥ 4`
(Yan, Zhou, manuscript, sha256 642a1268…).

**Formalization Note.** The value at `d = 0` is irrelevant: every statement using it has `1 ≤ d`. -/
noncomputable def alpha (d : ℕ) : ℝ :=
  if d ≤ 3 then 1 + √(d : ℝ) else 3

end FairFacilityLoc


