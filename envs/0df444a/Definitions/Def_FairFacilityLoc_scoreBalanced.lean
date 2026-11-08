-- Prove2me | Definitions.Def_FairFacilityLoc_scoreBalanced
-- name    : FairFacilityLoc_scoreBalanced
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:15:09.499459+00:00
-- url     : https://prove2.me/theorems/ebd5ae31-870e-4fc9-80f8-4d585bc4166f
-- title:
--   The Score-Balanced mechanism $M_d$, (2.4)
-- statement:
--   In each coordinate $r$, the **Score-Balanced mechanism** returns the smallest report at which the cut wins:
--   $$M_d(x;\mathcal G)_r=\min\bigl\{t\in\{x_{1r},\dots,x_{nr}\}:\ \max_j\sigma_j(L_r(t;x))\ge\max_j\sigma_j(N\setminus L_r(t;x))\bigr\}.$$
--
--   This is the mechanism of the mission's main results. The candidates are the reports of all agents, also for $d\ge4$.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), (2.4), p.16 (PDF p.18)

import Mathlib
import Definitions.Def_FairFacilityLoc_Mechanism
import Definitions.Def_FairFacilityLoc_cutOutput
import Definitions.Def_FairFacilityLoc_groupScore

namespace FairFacilityLoc

/-- **The Score-Balanced mechanism `M_d`** (Yan, Zhou, manuscript, sha256 642a1268…, (2.4), p.16, PDF p.18):
`M_d(x; G)_r = min {t ∈ {x_{1r}, …, x_{nr}} : max_j σ_j(L_r(t; x)) ≥ max_j σ_j(N ∖ L_r(t; x))}`.

**Formalization Note.** The candidates are the reports of all agents, also when `d ≥ 4`. For `d ≥ 4` the
weight sets play no role. -/
noncomputable def scoreBalanced (d : ℕ) (K : WeightSelection) : Mechanism d :=
  fun G x => cutOutput (fun _ S => IsWinning d K G S) x

end FairFacilityLoc


