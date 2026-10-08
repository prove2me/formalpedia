-- Prove2me | Definitions.Def_PriceOfStability_Undirected_ThreeNode
-- name    : PriceOfStability_Undirected_ThreeNode
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T01:15:56.419481+00:00
-- url     : https://prove2.me/theorems/1a8f0515-9dea-4c85-91be-0e6ce7ccd5f0
-- title:
--   Sect. 4 — the 3-node example with edge costs 2, 2 and 1 + ε
-- statement:
--   The example of Section 4 of Anshelevich et al. Let $G$ be the complete graph on three nodes $s, t_1, t_2$. Player 1 wants to connect $t_1$ with $s$ and player 2 wants to connect $t_2$ with $s$. The edge costs are
--   $$c_{(s,t_1)}=c_{(s,t_2)}=2,\qquad c_{(t_1,t_2)}=1+\varepsilon,$$
--   with $\varepsilon$ a real parameter. The game is the two-player undirected fair connection game on these data.
--
--   This instance shows that the bound $4/3$ of Claim 4.1 cannot be improved.
--
--   **Formalization Note.** The nodes are `0 = s`, `1 = t₁`, `2 = t₂` of `Fin 3`; the diagonal pairs $\{v,v\}$, which are not edges, get cost $0$ and never occur in a strategy.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1613 (PDF p. 12), Sect. 4, example before Claim 4.1

import Definitions.Def_PriceOfStability_Undirected_Model
open CongestionPoA.AsymSum

namespace PriceOfStability.Undirected

/-- Edge costs of the 3-node example of Sect. 4 (Anshelevich et al., SIAM J. Comput. 38 (2008),
p. 1613, PDF p. 12), on the vertices `0 = s`, `1 = t₁`, `2 = t₂`: the edges `(s, t₁)` and `(s, t₂)`
cost `2`, the edge `(t₁, t₂)` costs `1 + ε`.

**Formalization Note.** The diagonal pairs `s(v, v)` get cost `0`; they are not edges of a simple
graph and never belong to a strategy. -/
noncomputable def threeNodeCost (ε : ℝ) (e : Sym2 (Fin 3)) : ℝ :=
  if e = s(0, 1) ∨ e = s(0, 2) then 2 else if e = s(1, 2) then 1 + ε else 0

/-- The 3-node example of Sect. 4 (p. 1613, PDF p. 12): the complete graph on `{s, t₁, t₂}`
(`0, 1, 2`), common terminal `s = 0`, player `0` (the paper's player 1) connects `t₁ = 1` with `s`,
player `1` (the paper's player 2) connects `t₂ = 2` with `s`, edge costs `threeNodeCost ε`. -/
noncomputable def threeNode (ε : ℝ) : CongestionGame (Fin 2) (Sym2 (Fin 3)) :=
  twoPlayerGame ⊤ (threeNodeCost ε) 0 ![1, 2]

end PriceOfStability.Undirected


