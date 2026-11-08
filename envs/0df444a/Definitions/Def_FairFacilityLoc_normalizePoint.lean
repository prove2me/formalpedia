-- Prove2me | Definitions.Def_FairFacilityLoc_normalizePoint
-- name    : FairFacilityLoc_normalizePoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:12:22.647296+00:00
-- url     : https://prove2.me/theorems/97248c5a-d513-4fa7-b447-15f4184cbe70
-- title:
--   The normalization of Step 1
-- statement:
--   Given the output $y$ and a point $y^*\ne y$: translate so that $y$ becomes the origin, reflect every coordinate $r$ with $y^*_r<y_r$, scale by $1/\|y^*-y\|_2$, and multiply every weight by $c=\|y^*-y\|_2/F_W(y^*)$.
--
--   Then every effect is multiplied by $1/F_W(y^*)$, and $y^*$ goes to a unit vector $z\ge0$ with $F_W(z)=1$.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Step 1, p.21 (PDF p.23); family form p.49 (PDF p.51)

import Mathlib
import Definitions.Def_FairFacilityLoc_familyObjective

namespace FairFacilityLoc

/-- **The change of coordinates of Step 1** (Yan, Zhou, manuscript, sha256 642a1268…, p.21, PDF p.23): translate
so that `y` becomes the origin, reflect every coordinate `r` with `y*_r < y_r`, and scale by `1/∥y* − y∥₂`. -/
noncomputable def normalizePoint {d : ℕ} (y ystar p : GeoSemialgCSP.E d) : GeoSemialgCSP.E d :=
  WithLp.toLp 2 fun r => (if y r ≤ ystar r then p r - y r else y r - p r) / ‖ystar - y‖

/-- **The change of units of Step 1**, p.21, PDF p.23, for weight families as on p.49, PDF p.51: every weight
vector is multiplied by `c = ∥y* − y∥₂ / F_W(y*)`.

**Formalization Note.** `F_W` is the objective of the profile before the normalization. -/
noncomputable def normalizeWeights {n d : ℕ} (x : Fin n → GeoSemialgCSP.E d) (W : Finset (Fin n → ℝ)) (y ystar : GeoSemialgCSP.E d) :
    Finset (Fin n → ℝ) :=
  open Classical in W.image fun a => (‖ystar - y‖ / familyObjective x W ystar) • a

end FairFacilityLoc


