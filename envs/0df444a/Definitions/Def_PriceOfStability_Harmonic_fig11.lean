-- Prove2me | Definitions.Def_PriceOfStability_Harmonic_fig11
-- name    : PriceOfStability_Harmonic_fig11
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:39:48.581987+00:00
-- url     : https://prove2.me/theorems/27e390a5-433b-45a2-9fed-7fa9bada8f0c
-- title:
--   Fig. 1.1 — the k-player instance whose price of stability tends to H(k)
-- statement:
--   The instance of Fig. 1.1 of Anshelevich et al. Fix $k\in\mathbb N$ and $\varepsilon\in\mathbb R$. The graph has a source $s$, terminals $t_1,\dots,t_k$ and one further node $v$, with the edges
--
--   1. $s\to t_i$ of cost $1/i$ (the own path of player $i$), for $i=1,\dots,k$;
--   2. $s\to v$ of cost $1+\varepsilon$ (the common path);
--   3. $v\to t_i$ of cost $0$, for $i=1,\dots,k$.
--
--   Player $i$ connects $s$ to $t_i$, so its two strategies are $\{s\to t_i\}$ and $\{s\to v,\ v\to t_i\}$. Edge costs are constant in the number of users and shared equally (Shapley cost sharing).
--
--   For $\varepsilon>0$ the instance shows that the bound $H(k)$ on the price of stability cannot be improved.
--
--   **Formalization Note.** Players are indexed by $\{0,\dots,k-1\}$; player $i$ in Lean is the paper's player $i+1$, whose own edge costs $1/(i+1)$.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1604 (PDF p. 3), Fig. 1.1 and the preceding paragraph

import Mathlib
import Definitions.Def_PriceOfStability_Harmonic_Model

open CongestionPoA.AsymSum

namespace PriceOfStability.Harmonic

/-- The edges of the graph of Fig. 1.1 (Anshelevich et al., SIAM J. Comput. 38 (2008), p. 1604
(PDF p. 3)) with `k` players: player `i`'s own edge `s → tᵢ` (`own i`), the common edge from `s`
to the unlabelled bottom node `v` (`common`), and the edge `v → tᵢ` (`zero i`).
Player `i : Fin k` is the paper's player `i + 1`. -/
inductive Fig11Edge (k : ℕ) where
  | own (i : Fin k)
  | common
  | zero (i : Fin k)
  deriving DecidableEq, Fintype

/-- The edge costs of Fig. 1.1 (p. 1604): the own edge of the paper's player `i + 1` costs
`1/(i+1)`, the common edge costs `1 + ε`, and every edge `v → tᵢ` costs `0`. -/
noncomputable def fig11Cost (k : ℕ) (ε : ℝ) : Fig11Edge k → ℝ
  | .own i => 1 / ((i : ℕ) + 1 : ℝ)
  | .common => 1 + ε
  | .zero _ => 0

/-- The two `s`–`tᵢ` paths of player `i` in Fig. 1.1: its own edge, or the common edge followed
by its zero-cost edge `v → tᵢ`. -/
def fig11Strategies (k : ℕ) (i : Fin k) : Finset (Finset (Fig11Edge k)) :=
  {{Fig11Edge.own i}, {Fig11Edge.common, Fig11Edge.zero i}}

/-- The instance of Fig. 1.1 (p. 1604 (PDF p. 3)) as a fair (Shapley) cost-sharing game with
`k` players and constant edge costs `fig11Cost k ε`. -/
noncomputable def fig11 (k : ℕ) (ε : ℝ) : CongestionGame (Fin k) (Fig11Edge k) :=
  fairGame (fig11Strategies k) (fun e _ => fig11Cost k ε e)

end PriceOfStability.Harmonic


