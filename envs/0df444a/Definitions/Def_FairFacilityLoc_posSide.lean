-- Prove2me | Definitions.Def_FairFacilityLoc_posSide
-- name    : FairFacilityLoc_posSide
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:58.907088+00:00
-- url     : https://prove2.me/theorems/c09180c1-0f00-4f7e-b7a4-f120c1118af3
-- title:
--   The two sides of a coordinate
-- statement:
--   In normalized coordinates, the agents of coordinate $r$ split into $N^+_r=\{i:x_{ir}>0\}$ and $N^-_r=\{i:x_{ir}\le0\}$.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), §3.2.2, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E

namespace FairFacilityLoc

/-- The **positive side** `N⁺_r = {i : x_{ir} > 0}` of coordinate `r` (Yan, Zhou, manuscript, sha256 642a1268…,
§3.2.2, p.25, PDF p.27). -/
noncomputable def posSide {n d : ℕ} (x : Fin n → GeoSemialgCSP.E d) (r : Fin d) : Finset (Fin n) :=
  Finset.univ.filter fun i => 0 < x i r

/-- The **nonpositive side** `N⁻_r = {i : x_{ir} ≤ 0}` of coordinate `r`, §3.2.2, p.25, PDF p.27. -/
noncomputable def nonposSide {n d : ℕ} (x : Fin n → GeoSemialgCSP.E d) (r : Fin d) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i r ≤ 0

end FairFacilityLoc


