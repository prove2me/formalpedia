-- Prove2me | Definitions.Def_AutobidSPPE_winner
-- name    : AutobidSPPE_winner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:57:57.102511+00:00
-- url     : https://prove2.me/theorems/46f507ac-39bc-44e8-8b31-e77d3f6bfada
-- title:
--   Winner of the paced second-price auction
-- statement:
--   Given multipliers $\alpha\in\mathbb R^n$ and values $v\in\mathbb R^n$, bidder $j$ bids $\alpha_j v_j$. The **winner** is the bidder selected by the tie rule from the set of highest bidders
--   $$
--   \Big\{ j : \alpha_j v_j \ge \max_k \alpha_k v_k \Big\}.
--   $$
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Problem 1.1, p.4; §2.2, p.10

import Mathlib
import Definitions.Def_AutobidSPPE_TieRule

namespace AutobidSPPE

/-- The winner of the auction (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), Problem 1.1, p.4; §2.2, p.10): bidder `i` bids `αᵢvᵢ`; the
item goes to the bidder chosen by the tie rule among those whose bid attains `maxⱼ αⱼvⱼ`. -/
noncomputable def winner {n : ℕ} (tie : TieRule n) (α v : Fin n → ℝ) : Fin n :=
  tie.pick (Finset.univ.filter fun j => ∀ k, α k * v k ≤ α j * v j)

end AutobidSPPE


