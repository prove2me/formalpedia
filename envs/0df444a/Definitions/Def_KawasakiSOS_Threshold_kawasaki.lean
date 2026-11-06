-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_kawasaki
-- name    : KawasakiSOS_Threshold_kawasaki
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:04:04.720687+00:00
-- url     : https://prove2.me/theorems/6280457b-1dee-4c38-81c1-cafa41eaf510
-- title:
--   The Kawasaki dynamics $P$
-- statement:
--   The Kawasaki dynamics $P$ on $\Omega_{n,k}$ chooses an ordered pair $(i,j)$ of adjacent columns uniformly from the $2k$ possibilities. If $h(i)\ge1$, it proposes $h'=h-e_i+e_j$ and accepts with probability $\min\{1,\pi(h')/\pi(h)\}$. Otherwise it stays put. This matrix is the one-step transition matrix of that chain. The move conserves the total mass $n$.
--
--   **Formalization Note** The uniform choice is a sum over the $2k$ pairs (column, orientation). For $k=2$ the cycle has two parallel edges, so each of the ordered pairs $(0,1)$ and $(1,0)$ has probability $1/2$, as on p. 7 of the source.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 1 (PDF p. 2)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_moveProb
import Definitions.Def_KawasakiSOS_Threshold_stepSign

namespace KawasakiSOS.Threshold

/-- The non-lazy Kawasaki chain `P`: choose an ordered pair `(i, j)` of adjacent columns uniformly from the `2k` possibilities, then apply the Metropolis move. Formalization Note: the sum runs over the `2k` oriented choices `(i, s)`, so at `k = 2` the pair `(0, 1)` has probability `1/2` (p. 7).

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 1 (PDF p. 2). -/
noncomputable def kawasaki (n k : ℕ) [NeZero k] (lam : ℝ) : Matrix (Config n k) (Config n k) ℝ :=
  fun h h' => ∑ i : ZMod k, ∑ s : Bool, (1 / (2 * (k : ℝ))) * moveProb lam h h' i (i + stepSign s)

end KawasakiSOS.Threshold


