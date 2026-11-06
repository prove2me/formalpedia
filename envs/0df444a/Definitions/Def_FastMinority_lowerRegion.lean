-- Prove2me | Definitions.Def_FastMinority_lowerRegion
-- name    : FastMinority_lowerRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:26.282007+00:00
-- url     : https://prove2.me/theorems/09d35206-aeb3-49df-a095-d9946f66271f
-- title:
--   Lower region $\mathcal L=[1,L-1]$
-- statement:
--   The **lower region** is the set of minority sizes $\mathcal L=[1,L-1]$, $L=\lceil n/(4k)\rceil$. In it the minority size multiplies by at least $k/2$ per round with high probability (Lemma 3.5).
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Section 3, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_FastMinority_lowThr

set_option autoImplicit false

open Classical

namespace FastMinority

/-- The **lower region** `𝓛 = [1, L − 1]` (Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), §3, p.6 = PDF p.8), `L = ⌈n/(4k)⌉`, as a set of
minority counts. -/
noncomputable def lowerRegion (n k : ℕ) : Set (Fin (n + 1)) :=
  {x | 1 ≤ (x : ℕ) ∧ (x : ℕ) < lowThr n k}

end FastMinority


