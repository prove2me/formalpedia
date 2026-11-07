-- Prove2me | Definitions.Def_OnlineCAP_VirtualPt
-- name    : OnlineCAP_VirtualPt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:41.982202+00:00
-- url     : https://prove2.me/theorems/57889622-c8bb-4604-91a6-96742dc2bb8b
-- title:
--   Virtual points 𝒫 = P × [n]
-- statement:
--   For a finite point set $P$ with $n=|P|$, the **virtual points** are $\mathcal P=P\times[n]$: $n$ copies $(p,0),\dots,(p,n-1)$ of each physical point $p$, so $|\mathcal P|=n^2$. The projection $\pi:\mathcal P\to P$ maps a copy to its physical parent.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), §4.1.2, p.16

import Mathlib

namespace OnlineCAP

/-- **Virtual points.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §4.1.2, "New point set", p.16 (PDF p.16): "construct a new universe
of virtual points 𝒫 = P × [n], consisting of n virtual copies for each physical point p ∈ P
(yielding N = |𝒫| = n²). We denote by π : 𝒫 → P the projection mapping each virtual point
e = (p, i) to its physical parent p".

`VirtualPt P = P × Fin n` with `n = |P|`; the projection `π` is `Prod.fst`, and the copies of `p`
are `(p, 0), …, (p, n − 1)`. -/
abbrev VirtualPt (P : Finset (ℝ × ℝ)) : Type := ↥P × Fin P.card

end OnlineCAP


