-- Prove2me | Definitions.Def_Grunbaum2003_IsRayFaceLatticeOutput
-- name    : Grunbaum2003_IsRayFaceLatticeOutput
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:36:22.151985+00:00
-- url     : https://prove2.me/theorems/0dedbc7c-6ba7-495a-8cd8-542874d625ea
-- title:
--   Complete face lattice output
-- statement:
--   A self delimiting Boolean inclusion matrix bijectively enumerating every exposed face.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §3.6, printed pp. 52b–52c / PDF pp. 74–75; exact-real ray-machine expression adapter; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_RayConfiguration
import Mathlib.Order.Hom.Basic

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

def IsRayFaceLatticeOutput {d : ℕ} (P : Set (Fin d → ℝ))
    (c : RayConfiguration) : Prop :=
  ∃ n : ℕ,
    (∀ i : Fin n, c.tape (c.head + (i.val : ℤ)) = 1) ∧
    c.tape (c.head + (n : ℤ)) = 0 ∧
    ∃ e : Fin n ≃ PolytopeFace P, ∀ i j : Fin n,
      let bit := c.tape (c.head + ((n + 1 + i.val * n + j.val : ℕ) : ℤ))
      (bit = 0 ∨ bit = 1) ∧ (bit = 1 ↔ e i ≤ e j)

end Grunbaum2003


