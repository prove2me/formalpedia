-- Prove2me | Definitions.Def_CrossLayerControl_ECCA_zeroAt
-- name    : CrossLayerControl_ECCA_zeroAt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:43:49.275957+00:00
-- url     : https://prove2.me/theorems/4083755a-897e-4f88-97f9-c8ea00a65a91
-- title:
--   The vector $P[i]$ with the $i$-th entry set to zero
-- statement:
--   For a vector $P\in\mathbb R^L$ and a link $i$, $P[i]$ is the vector equal to $P$ except that its $i$-th entry is $0$.
--
--   It appears in the $\beta$-condition, which compares the rate of link $i$ under $P$ with its rate when link $i$ is switched off.
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, p. 115

import Mathlib

namespace CrossLayerControl.ECCA

/-- **The power vector with one entry set to zero, P[i].**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), p. 115 (unnumbered): "where P = (P1,...,PL), and P[i] is equal to
P with the exception that the ith entry is set to zero."

`zeroAt P i` is the vector equal to `P` except that its `i`-th entry is `0`. -/
def zeroAt {L : ℕ} (P : Fin L → ℝ) (i : Fin L) : Fin L → ℝ := Function.update P i 0

end CrossLayerControl.ECCA


