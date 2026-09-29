-- Prove2me | Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
-- name    : Grunbaum2003_IsPolytopeRayOracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:34:53.335708+00:00
-- url     : https://prove2.me/theorems/99b140d4-390d-444f-99f0-a06cfd8438a3
-- title:
--   Boundary point ray oracle
-- statement:
--   For each nonzero direction, the oracle returns a boundary point on its positive ray.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §3.6, printed pp. 52b–52c / PDF pp. 74–75; exact-real ray-machine expression adapter; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

def IsPolytopeRayOracle {d : ℕ} (P : Set (Fin d → ℝ))
    (oracle : (Fin d → ℝ) → (Fin d → ℝ)) : Prop :=
  ∀ v, v ≠ 0 → oracle v ∈ frontier P ∧ ∃ t : ℝ, 0 < t ∧ oracle v = t • v

end Grunbaum2003


