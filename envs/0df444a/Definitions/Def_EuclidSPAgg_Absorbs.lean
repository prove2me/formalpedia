-- Prove2me | Definitions.Def_EuclidSPAgg_Absorbs
-- name    : EuclidSPAgg_Absorbs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:41:10.909882+00:00
-- url     : https://prove2.me/theorems/6061e3f0-9c21-410e-89a8-f76deedb3218
-- title:
--   Absorbing identity (3.1)
-- statement:
--   Let $f:E^n\to E$ with $n=m+2$, and $g:E^{n-2}\to E$. The map $g$ **absorbs** $f$ if
--   $$
--   f(a,g(z),z)=g(z)\qquad(a\in E,\ z\in E^{n-2}):
--   $$
--   if one agent reports $g(z)$ and $n-2$ others report $z$, the outcome is $g(z)$ whatever the last agent reports.
--
--   **Formalization Note** The profile $(a,g(z),z)$ puts $a$ first, $g(z)$ second and then $z$, in the printed order.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Proposition 3.2, display (3.1), p.13 (PDF p.15)

import Mathlib
import Definitions.Def_EuclidSPAgg_Mech
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- The absorbing identity (3.1) (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), Proposition 3.2, p.13 (PDF p.15)): for a mechanism `f` on
`n = m + 2` reports, `g : E^{n−2} → E` satisfies `f(a, g(z), z) = g(z)` for all `a ∈ E` and
`z ∈ E^{n−2}`.

**Formalization Note** The profile `(a, g(z), z)` is `Matrix.vecCons a (Matrix.vecCons (g z) z)`:
the free report in position 0, the absorber value in position 1, then `z`, in the printed order. -/
def Absorbs {m d : ℕ} (f : Mech (m + 2) d) (g : Mech m d) : Prop :=
  ∀ (a : E d) (z : Fin m → E d), f (Matrix.vecCons a (Matrix.vecCons (g z) z)) = g z

end EuclidSPAgg


