-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_highestOtherT
-- name    : AutobidSPPE_Supplement_highestOtherT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:38:30.179911+00:00
-- url     : https://prove2.me/theorems/cc8656ba-f1ea-4e82-8e6b-0729a480f070
-- title:
--   Throttling payment $\max_{j\ne i,\,\xi_j=1}v_j$
-- statement:
--   When bidder $i$ wins the throttled auction with participation set $P$, it pays the highest value among the **other participants**,
--   $$
--   \max_{j\in P\setminus\{i\}} v_j ,
--   $$
--   and a sole participant pays zero ($\max\emptyset=0$).
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Problem 1.2, p.4; §3.2, p.26; (53), p.27

import Mathlib

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- The throttling payment `maxⱼ≠ᵢ, ξⱼ=1 vⱼ` of bidder `i` when it wins: the highest value among the
other participants (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), Problem 1.2, p.4; §3.2, p.26; `Mᵢ` of (53), p.27). A sole participant pays zero
(`max ∅ = 0`). -/
noncomputable def highestOtherT {n : ℕ} (P : Finset (Fin n)) (v : Fin n → ℝ) (i : Fin n) : ℝ :=
  if h : (P.erase i).Nonempty then (P.erase i).sup' h v else 0

end AutobidSPPE.Supplement


