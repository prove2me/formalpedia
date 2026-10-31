-- Prove2me | Definitions.Def_StrategyproofMultidim_pivotal
-- name    : StrategyproofMultidim_pivotal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:19.037863+00:00
-- url     : https://prove2.me/theorems/13829c82-d54f-42cb-833a-2e4f68ad3270
-- title:
--   The Pivotal mechanism $\mu^P$ with Remark 1's tie-break
-- statement:
--   The concrete **Pivotal mechanism** $\mu^P$: each object $k$ is sold to the buyer of least index among those reporting the highest value for $k$ (Remark 1's order $1\succ2\succ\dots\succ n$), and a buyer pays, for each object it wins, the highest value reported for that object by the other buyers:
--   $$p_i(v)=\sum_{k:\,d_i^k(v)=1}\max_{j\neq i}v_j^k .$$
--   This is $m$ simultaneous second-price auctions, one per object.
--
--   **Formalization Note** For $n=1$ the single buyer gets every object at price $0$.
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), Definition 7, p.15 (PDF p.16); Remark 1, p.11 (PDF p.12); p.16 (PDF p.17)

import Mathlib
import Definitions.Def_StrategyproofMultidim_Mechanism
import Definitions.Def_StrategyproofMultidim_maxOthers

namespace StrategyproofMultidim

/-- **The Pivotal mechanism `μᴾ` with the tie-break of Remark 1** (Definition 7, p.15;
Remark 1, p.11; p.16).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.11 (Remark 1): "Without loss of generality, henceforth we assume that at any such
profile v, the object k would be sold to the maximal agent in Sᵛ according to the linear order
1 ≻ 2 ≻ …… ≻ n." p.16: "the Pivotal mechanism is equivalent to executing m different 'Second
Price Auction's - one for each object to be sold."

Object `k` is sold to the buyer of least index among those reporting the highest value for `k`;
buyer `i` pays, for each object it wins, the highest value reported for that object by the other
buyers (`maxOthers`).

**Formalization Note.** Buyer `1 ≻ 2 ≻ … ≻ n` is Lean index `0, 1, …, n-1`, so the least index
wins ties. For `n = 1` the single buyer gets every object at price `0`. -/
noncomputable def pivotal (n m : ℕ) : Mechanism n m where
  q v i k := decide ((∀ j, v j k ≤ v i k) ∧ ∀ j, j < i → v j k < v i k)
  t i v := ∑ k ∈ Finset.univ.filter
      (fun k => decide ((∀ j, v j k ≤ v i k) ∧ ∀ j, j < i → v j k < v i k) = true),
    maxOthers v i k

end StrategyproofMultidim


