-- Prove2me | Definitions.Def_FastMinority_lowThr
-- name    : FastMinority_lowThr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:23.47105+00:00
-- url     : https://prove2.me/theorems/1fae0f20-2e44-48f5-be41-e4f91c71e18c
-- title:
--   Lower threshold $L=\lceil n/(4k)\rceil$
-- statement:
--   The **lower threshold** is
--   $$
--   L=\lceil n/(4k)\rceil .
--   $$
--   Below it, the minority size grows by a factor of order $k$ per round with high probability. It bounds the lower region $\mathcal L=[1,L-1]$ and the core region from below.
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Section 3, p.6 (PDF p.8)

import Mathlib

set_option autoImplicit false

open Classical

namespace FastMinority

/-- The lower threshold `L = ⌈n/(4k)⌉` (Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), §3, p.6 = PDF p.8).

**Formalization Note** `⌈·⌉₊` is the natural-number ceiling of a nonnegative real. -/
noncomputable def lowThr (n k : ℕ) : ℕ :=
  ⌈(n : ℝ) / (4 * k)⌉₊

end FastMinority


