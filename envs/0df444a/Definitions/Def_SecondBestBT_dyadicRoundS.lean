-- Prove2me | Definitions.Def_SecondBestBT_dyadicRoundS
-- name    : SecondBestBT_dyadicRoundS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:42:46.29729+00:00
-- url     : https://prove2.me/theorems/2fe70ca4-d27b-4667-b842-006c30f34e58
-- title:
--   Seller's dyadic rounding $\pi^M_S(s)=\lceil 2^M s\rceil/2^M$
-- statement:
--   For the dyadic mesh $t_k=k2^{-M}$, a seller value in $(t_{k-1},t_k]$ is rounded **up** to $t_k$, and $0$ is kept:
--   $$
--   \pi^M_S(s)=\lceil 2^M s\rceil/2^M,\qquad 0\le \pi^M_S(s)-s\le 2^{-M}\ \text{ on } [0,1].
--   $$
--   The rounded seller prior $\hat F^M_S$ is the law of $\pi^M_S(s)$ for $s\sim F_S$.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 3, p.6

import Mathlib

namespace SecondBestBT

/-- The seller's dyadic rounding map `π^M_S(s) = ⌈2^M s⌉ / 2^M` (Liu–Qin–Ren–Wang,
arXiv:2606.03849, held version sha256 17184930…, Section 3, p.6): sellers in `(t_{k−1}, t_k]` are
rounded **up** to `t_k = k 2^{−M}`, and `π^M_S(0) = 0`.

**Formalization Note** `⌈·⌉₊` is the natural-number ceiling; on `[0, 1]`, the domain of the
paper's map, it agrees with the integer ceiling. -/
noncomputable def dyadicRoundS (M : ℕ) (s : ℝ) : ℝ :=
  (⌈(2 : ℝ) ^ M * s⌉₊ : ℝ) / 2 ^ M

end SecondBestBT


