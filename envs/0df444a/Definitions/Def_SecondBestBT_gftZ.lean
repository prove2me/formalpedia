-- Prove2me | Definitions.Def_SecondBestBT_gftZ
-- name    : SecondBestBT_gftZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:42:59.95461+00:00
-- url     : https://prove2.me/theorems/6ef1291a-af2b-42ce-9e97-1b4299c9fb2d
-- title:
--   Gains from trade on the integer grid $Z_W$
-- statement:
--   For priors $f_S,f_B$ on $Z_W=\{0,\dots,W\}$ and an allocation $x:Z_W^2\to[0,1]$,
--   $$
--   \mathrm{GFT}(x)=\sum_{s,b=0}^{W}x(s,b)\,f_S(s)\,f_B(b)\,(b-s).
--   $$
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 4.1, p.8; display on p.13

import Mathlib

namespace SecondBestBT

/-- The gains from trade of an allocation `x : Z_W² → [0, 1]` under priors `f_S, f_B` on
`Z_W = {0, …, W}`: `GFT(x) = ∑_{s,b} x(s, b) f_S(s) f_B(b) (b − s)` (Liu–Qin–Ren–Wang,
arXiv:2606.03849, held version sha256 17184930…, Section 4.1, p.8, and the expanded display on
p.13).

**Formalization Note** An allocation is a matrix `x : ℕ → ℕ → ℝ` indexed `x s b`, seller value
first; only entries with `s, b ≤ W` are used. -/
def gftZ (fS fB : ℕ → ℝ) (W : ℕ) (x : ℕ → ℕ → ℝ) : ℝ :=
  ∑ s ∈ Finset.range (W + 1), ∑ b ∈ Finset.range (W + 1), x s b * fS s * fB b * ((b : ℝ) - s)

end SecondBestBT


