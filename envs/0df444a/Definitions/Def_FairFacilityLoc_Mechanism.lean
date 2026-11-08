-- Prove2me | Definitions.Def_FairFacilityLoc_Mechanism
-- name    : FairFacilityLoc_Mechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:12:16.380542+00:00
-- url     : https://prove2.me/theorems/ce3dc65d-af05-4357-9a3d-67c936935f2f
-- title:
--   Deterministic mechanism
-- statement:
--   A **mechanism** in dimension $d$ maps a profile $x\in(\mathbb R^d)^n$ and a public group structure $\mathcal G$ to a facility location $M(x;\mathcal G)\in\mathbb R^d$, for all numbers $n$ of agents and $m$ of groups. All mechanisms of the paper are deterministic.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), §2.1, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E
import Definitions.Def_FairFacilityLoc_GroupStructure

namespace FairFacilityLoc

/-- A **deterministic mechanism** in dimension `d` (Yan, Zhou, manuscript, sha256 642a1268…, §2.1, p.15,
PDF p.17): it maps the profile and the public group structure to a facility location.

**Formalization Note.** One map serves all `n`, `m` and all sublinear group structures, as printed
(`M(x; G)`), and determinism is built into the type. -/
abbrev Mechanism (d : ℕ) : Type :=
  ∀ {n m : ℕ}, GroupStructure n m → (Fin n → GeoSemialgCSP.E d) → GeoSemialgCSP.E d

end FairFacilityLoc


