-- Prove2me | Definitions.Def_FairFacilityLoc_sideLength
-- name    : FairFacilityLoc_sideLength
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:11:26.629335+00:00
-- url     : https://prove2.me/theorems/e94c070e-c013-4403-a81f-bd1c3a7dcb05
-- title:
--   Supports and side lengths
-- statement:
--   The **support** of agent $i$ is $S^+_i=\{r:x_{ir}>0\}$, with complement $S^-_i=\{r:x_{ir}\le0\}$. For a set $Z$ of coordinates, $z_Z$ agrees with $z$ on $Z$ and vanishes elsewhere. The side lengths of a weight vector $a$ are
--   $$L^\pm(a)=\sum_{i\in N}a_i\,\|z_{S^\pm_i}\|_2 .$$
--
--   For a linear group $a=w_j\mathbf 1_{G_j}$ these are the lengths $L^\pm_j$ of (3.3); the form with $a$ is the one of the proof of Proposition 3.27.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), (3.3), §3.2.1, p.21 (PDF p.23); Proposition 3.27, p.48 (PDF p.50)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E

namespace FairFacilityLoc

/-- The **support** `S⁺_i = {r : x_{ir} > 0}` of agent `i` (Yan, Zhou, manuscript, sha256 642a1268…, §3.2.1,
p.21, PDF p.23). -/
noncomputable def posSupport {n d : ℕ} (x : Fin n → GeoSemialgCSP.E d) (i : Fin n) : Finset (Fin d) :=
  Finset.univ.filter fun r => 0 < x i r

/-- The complement `S⁻_i = {r : x_{ir} ≤ 0}` of the support, §3.2.1, p.21, PDF p.23. -/
noncomputable def nonposSupport {n d : ℕ} (x : Fin n → GeoSemialgCSP.E d) (i : Fin n) : Finset (Fin d) :=
  Finset.univ.filter fun r => x i r ≤ 0

/-- The vector `z_Z`, which agrees with `z` on `Z` and is zero elsewhere, §3.2.1, p.21, PDF p.23. -/
noncomputable def restrictCoords {d : ℕ} (z : GeoSemialgCSP.E d) (Z : Finset (Fin d)) : GeoSemialgCSP.E d :=
  WithLp.toLp 2 fun r => if r ∈ Z then z r else 0

/-- The **positive-side length** `L⁺(a) = ∑_{i ∈ N} a_i ∥z_{S⁺_i}∥₂`, (3.3), p.21, PDF p.23, in the form of the
proof of Proposition 3.27, p.48, PDF p.50. For a linear group `a = w_j 1_{G_j}` it is the printed `L⁺_j`. -/
noncomputable def posLength {n d : ℕ} (x : Fin n → GeoSemialgCSP.E d) (z : GeoSemialgCSP.E d) (a : Fin n → ℝ) : ℝ :=
  ∑ i, a i * ‖restrictCoords z (posSupport x i)‖

/-- The **nonpositive-side length** `L⁻(a) = ∑_{i ∈ N} a_i ∥z_{S⁻_i}∥₂`, (3.3), p.21, PDF p.23, in the form of the
proof of Proposition 3.27, p.48, PDF p.50. -/
noncomputable def nonposLength {n d : ℕ} (x : Fin n → GeoSemialgCSP.E d) (z : GeoSemialgCSP.E d) (a : Fin n → ℝ) : ℝ :=
  ∑ i, a i * ‖restrictCoords z (nonposSupport x i)‖

end FairFacilityLoc


