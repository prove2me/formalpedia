-- Prove2me | Definitions.Def_SecondBestBT_dyadicRoundB
-- name    : SecondBestBT_dyadicRoundB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:00.520819+00:00
-- url     : https://prove2.me/theorems/fea5af58-73b7-46f9-8662-23c7b75bccb8
-- title:
--   Buyer's dyadic rounding $\pi^M_B(b)=\lfloor 2^M b\rfloor/2^M$
-- statement:
--   For the dyadic mesh $t_k=k2^{-M}$, a buyer value in $[t_k,t_{k+1})$ is rounded **down** to $t_k$, and $1$ is kept:
--   $$
--   \pi^M_B(b)=\lfloor 2^M b\rfloor/2^M,\qquad 0\le b-\pi^M_B(b)\le 2^{-M}\ \text{ on } [0,1].
--   $$
--   The rounded buyer prior $\hat F^M_B$ is the law of $\pi^M_B(b)$ for $b\sim F_B$.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 3, p.6

import Mathlib

namespace SecondBestBT

/-- The buyer's dyadic rounding map `π^M_B(b) = ⌊2^M b⌋ / 2^M` (Liu–Qin–Ren–Wang,
arXiv:2606.03849, held version sha256 17184930…, Section 3, p.6): buyers in `[t_k, t_{k+1})` are
rounded **down** to `t_k = k 2^{−M}`, and `π^M_B(1) = 1`.

**Formalization Note** `⌊·⌋₊` is the natural-number floor; on `[0, 1]` it agrees with the integer
floor. -/
noncomputable def dyadicRoundB (M : ℕ) (b : ℝ) : ℝ :=
  (⌊(2 : ℝ) ^ M * b⌋₊ : ℝ) / 2 ^ M

end SecondBestBT


