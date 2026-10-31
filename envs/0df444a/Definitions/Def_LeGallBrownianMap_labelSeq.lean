-- Prove2me | Definitions.Def_LeGallBrownianMap_labelSeq
-- name    : LeGallBrownianMap_labelSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:08.016775+00:00
-- url     : https://prove2.me/theorems/a9f1a23b-9604-4f36-ac55-c545b5cf5081
-- title:
--   The label function $\Lambda^\theta_i=\ell_{v_i}$
-- statement:
--   For a labeled $p$-tree $\theta=(\tau,\ell)$ the **label function** is the sequence $\Lambda^\theta_i=\ell_{v_i}$, $0\le i\le pn$, the labels read along the contour sequence (extended periodically). By condition (b), $\Lambda^\theta_{i+1}\ge\Lambda^\theta_i-1$.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.1, p.9

import Mathlib
import Definitions.Def_LeGallBrownianMap_contourSeq

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.1, p.9:
"The label function of θ = (τ, (ℓ_v)_{v∈τ°}) is the discrete sequence (Λ^θ_0, Λ^θ_1, ..., Λ^θ_{pn})
defined by Λ^θ_i = ℓ_{v_i} for every 0 ≤ i ≤ pn."

`labelSeq θ i = Λ^θ_i = ℓ_{v_i}`, with the contour sequence extended periodically (p.10). -/
def labelSeq (θ : Finset (List ℕ+) × (List ℕ+ → ℤ)) (i : ℕ) : ℤ :=
  θ.2 (contourSeq θ.1 i)

end LeGallBrownianMap


