-- Prove2me | Definitions.Def_FairFacilityLoc_share
-- name    : FairFacilityLoc_share
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:13:05.541987+00:00
-- url     : https://prove2.me/theorems/f4a375cc-4d87-4044-9c40-abe7d8e7c276
-- title:
--   The factor $\kappa$, the share $s_r$ and the number $v_r$
-- statement:
--   Under the assumption $\mathcal C>d$: $\kappa=\sqrt{d/\mathcal C}$ and the **share** of coordinate $r$ is $s_r=\kappa^2z_r^2K_r$. For $d\in\{2,3\}$, $v_r=\sqrt{(1-z_r^2)/(d-1)}$.
--
--   The shares sum to $d$, which the proof of Proposition 3.17 contradicts.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), p.36 (PDF p.38); p.43 (PDF p.45)

import Mathlib
import Definitions.Def_FairFacilityLoc_capacity

namespace FairFacilityLoc

/-- **The factor `κ = √(d/C)`** (Yan, Zhou, manuscript, sha256 642a1268…, p.36, PDF p.38), used under `C > d`. -/
noncomputable def kappa {n d : ℕ} (b : ℝ) (W : Finset (Fin n → ℝ)) (x : Fin n → GeoSemialgCSP.E d) (z : GeoSemialgCSP.E d) : ℝ :=
  √((d : ℝ) / weightedCapacity b W x z)

/-- **The share `s_r = κ² z_r² K_r`** of coordinate `r`, p.36, PDF p.38. The formula gives the printed `s_r = 0`
when `z_r = 0`. -/
noncomputable def share {n d : ℕ} (b : ℝ) (W : Finset (Fin n → ℝ)) (x : Fin n → GeoSemialgCSP.E d) (z : GeoSemialgCSP.E d) (r : Fin d) :
    ℝ :=
  kappa b W x z ^ 2 * z r ^ 2 * capacity b W x r

/-- **`v_r = √((1 − z_r²)/(d − 1))`**, p.43, PDF p.45, as a function of `t = z_r`; used for `d ∈ {2, 3}`, so the
division is by a nonzero number. -/
noncomputable def vCoord (d : ℕ) (t : ℝ) : ℝ :=
  √((1 - t ^ 2) / ((d : ℝ) - 1))

end FairFacilityLoc


