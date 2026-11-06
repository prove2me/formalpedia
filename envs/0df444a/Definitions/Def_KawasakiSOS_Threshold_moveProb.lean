-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_moveProb
-- name    : KawasakiSOS_Threshold_moveProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:02:47.470265+00:00
-- url     : https://prove2.me/theorems/8b0a5d83-ec4f-4b85-a036-2f1d9b2a923f
-- title:
--   One Metropolis move on a chosen ordered pair
-- statement:
--   Given that the ordered pair $(i,j)$ of columns has been chosen at state $h$: if $h(i)\ge1$, the chain proposes $h'=h-e_i+e_j$ and accepts with the Metropolis probability $\min\{1,\pi(h')/\pi(h)\}$, staying at $h$ otherwise. If $h(i)=0$ it stays at $h$. This definition is the probability of moving to a given state under that rule.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 1 (PDF p. 2)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_gibbs
import Definitions.Def_KawasakiSOS_Threshold_transfer

namespace KawasakiSOS.Threshold

/-- The law of the next state given that the ordered pair `(i, j)` was chosen: if `h(i) ≥ 1`, propose `h′ = h − e_i + e_j` and accept with probability `min{1, π(h′)/π(h)}`; otherwise stay.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 1 (PDF p. 2). -/
noncomputable def moveProb {n k : ℕ} [NeZero k] (lam : ℝ) (h h' : Config n k) (i j : ZMod k) : ℝ :=
  if 1 ≤ h.1 i then
    (if h' = transfer h i j then min 1 (gibbs n k lam (transfer h i j) / gibbs n k lam h) else 0) +
      (if h' = h then 1 - min 1 (gibbs n k lam (transfer h i j) / gibbs n k lam h) else 0)
  else if h' = h then 1 else 0

end KawasakiSOS.Threshold


