-- Prove2me | Definitions.Def_SecondBestBT_fbZ
-- name    : SecondBestBT_fbZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:05.648512+00:00
-- url     : https://prove2.me/theorems/cf3b5ece-6c80-4ee3-87f8-9f5181fbb171
-- title:
--   First-best gains from trade on $Z_W$
-- statement:
--   For priors $f_S,f_B$ on $Z_W$,
--   $$
--   \mathrm{FB}=\sum_{b}\sum_{s<b}(b-s)\,f_B(b)\,f_S(s)=\sum_{s,b=0}^W f_S(s)f_B(b)(b-s)^+ .
--   $$
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), display on p.13

import Mathlib

namespace SecondBestBT

/-- The first-best gains from trade on the integer grid,
`FB = ∑_b ∑_{s<b} (b − s) f_B(b) f_S(s) = ∑_{s,b} f_S(s) f_B(b) (b − s)⁺` (Liu–Qin–Ren–Wang,
arXiv:2606.03849, held version sha256 17184930…, Section 4.4, display on p.13). -/
def fbZ (fS fB : ℕ → ℝ) (W : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (W + 1), ∑ b ∈ Finset.range (W + 1), fS s * fB b * max ((b : ℝ) - s) 0

end SecondBestBT


