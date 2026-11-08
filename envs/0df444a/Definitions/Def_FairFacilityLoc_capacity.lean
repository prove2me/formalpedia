-- Prove2me | Definitions.Def_FairFacilityLoc_capacity
-- name    : FairFacilityLoc_capacity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:12:14.729079+00:00
-- url     : https://prove2.me/theorems/ac3ccbb4-b8da-4b55-bd30-633c49e8c259
-- title:
--   Capacities and positive-side scores
-- statement:
--   For a family $W$ and $z$: the **capacity** of coordinate $r$ is $K_r=\sigma_W(N^-_r)$, the **positive-side score** is $Q_r(a)=\sigma(N^+_r;a)$, and
--   $$\bar Q(a)=\sum_rz_r^2Q_r(a),\qquad \mathcal C=\sum_rz_r^2K_r.$$
--   A coordinate $r^*$ with the largest entry has $z_{r^*}=\max_rz_r$. A **dominating vector** of coordinate $r$ is an $a\in W$ with $\sigma(N^-_r;a)=K_r$.
--
--   These are the family forms of the capacities, scores and dominating groups of §3.2.2–3.2.3.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), §3.2.2, p.26 (PDF p.28); §3.2.3, p.33 (PDF p.35); family form p.48 (PDF p.50)

import Mathlib
import Definitions.Def_FairFacilityLoc_posSide
import Definitions.Def_FairFacilityLoc_weightScore

namespace FairFacilityLoc

/-- The **capacity** `K_r = σ_W(N⁻_r)` of coordinate `r`, the largest score of the nonpositive side (Yan, Zhou,
manuscript, sha256 642a1268…, §3.2.2, p.26, PDF p.28, in the family form of p.48, PDF p.50). -/
noncomputable def capacity {n d : ℕ} (b : ℝ) (W : Finset (Fin n → ℝ)) (x : Fin n → GeoSemialgCSP.E d) (r : Fin d) : ℝ :=
  maxWeightScore b W (nonposSide x r)

/-- The **positive-side score** `Q_r(a) = σ(N⁺_r; a)`, §3.2.2, p.26, PDF p.28. -/
noncomputable def posScore {n d : ℕ} (b : ℝ) (x : Fin n → GeoSemialgCSP.E d) (a : Fin n → ℝ) (r : Fin d) : ℝ :=
  weightScore b a (posSide x r)

/-- The **weighted score** `Q̄(a) = ∑_r z_r² Q_r(a)`, §3.2.2, p.26, PDF p.28. -/
noncomputable def weightedScore {n d : ℕ} (b : ℝ) (x : Fin n → GeoSemialgCSP.E d) (z : GeoSemialgCSP.E d) (a : Fin n → ℝ) : ℝ :=
  ∑ r, z r ^ 2 * posScore b x a r

/-- The **weighted capacity** `C = ∑_r z_r² K_r`, §3.2.2, p.26, PDF p.28. -/
noncomputable def weightedCapacity {n d : ℕ} (b : ℝ) (W : Finset (Fin n → ℝ)) (x : Fin n → GeoSemialgCSP.E d) (z : GeoSemialgCSP.E d) :
    ℝ :=
  ∑ r, z r ^ 2 * capacity b W x r

/-- `r` is **a coordinate with the largest entry**, `z_{r*} = max_r z_r`, §3.2.2, p.26, PDF p.28. -/
def IsTopCoord {d : ℕ} (z : GeoSemialgCSP.E d) (r : Fin d) : Prop :=
  ∀ k, z k ≤ z r

/-- `a` is a **dominating vector of coordinate `r`**: `a ∈ W` with `σ(N⁻_r; a) = K_r`, the family form of the
dominating group of §3.2.3, p.33, PDF p.35. -/
def IsDominating {n d : ℕ} (b : ℝ) (W : Finset (Fin n → ℝ)) (x : Fin n → GeoSemialgCSP.E d) (r : Fin d) (a : Fin n → ℝ) :
    Prop :=
  a ∈ W ∧ weightScore b a (nonposSide x r) = capacity b W x r

end FairFacilityLoc


