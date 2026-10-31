-- Prove2me | Definitions.Def_CongestionApproxPNE_gadget
-- name    : CongestionApproxPNE_gadget
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:15:53.275657+00:00
-- url     : https://prove2.me/theorems/e1f8020d-d75a-4335-b9cc-0ad504647d54
-- title:
--   The nonexistence gadget $\mathcal G^d_{(n,k,w,\beta)}$
-- statement:
--   Fix a degree $d\ge 2$ and parameters $n\in\mathbb N$, $k\in\{1,\dots,d\}$, $w\in(0,1]$, $\beta\in[0,1]$. The game $\mathcal G^d_{(n,k,w,\beta)}$ has $n+1$ players: a **heavy player** $0$ of weight $1$ and **light players** $1,\dots,n$ of weight $w$. It has $2(n+1)$ resources $a_0,\dots,a_n,b_0,\dots,b_n$; the hubs $a_0,b_0$ have cost $c_0(x)=x^k$ and all other resources have cost $c_1(x)=\beta x^d$. Each player has exactly two strategies:
--
--   $$
--   S_0=\bigl\{\{a_0,\dots,a_n\},\{b_0,\dots,b_n\}\bigr\},\qquad S_i=\bigl\{\{a_0,b_i\},\{b_0,a_i\}\bigr\}\quad(i=1,\dots,n).
--   $$
--
--   The heavy player wants to avoid the light players on her hub, while each light player wants to avoid the heavy player; the two incentives cannot both be satisfied, which is the source of Theorem 1's nonexistence bound.
--
--   **Formalization Note** Players are `Fin (n+1)` (player `0` heavy); resources are `Fin ((n+1)+(n+1))` with $a_i$ = `Fin.castAdd (n+1) i` and $b_i$ = `Fin.natAdd (n+1) i`. The light weight is $w\in\mathbb R_{\ge 0}$ with $w>0$ (weights are positive in §2; the family's $w=0$ is not a game). Restrictions on $k$, $w\le 1$ and $\beta$ are hypotheses of the theorems, not of the definition.
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, §3, p.4 (PDF p.5), the family G^d_(n,k,w,β)

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game

set_option autoImplicit false
open scoped NNReal

namespace CongestionApproxPNE

open HarksKlimm.Consistency

/-- **The nonexistence gadget `G^d_(n,k,w,β)`.**
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, arXiv:2002.07466v3, §3, p.4: "In
G^d_(n,k,w,β) there are n + 1 players: a heavy player of weight 1 and n light players 1, . . . , n
of equal weights w. There are 2(n + 1) resources a0, a1, . . . , an, b0, b1, . . . , bn where a0
and b0 have the same cost function c0 and all other resources a1, . . . , an, b1, . . . , bn have
the same cost function c1 given by c0(x) = x^k and c1(x) = βx^d. Each player has exactly two
strategies, and the strategy sets are given by S0 = {{a0, . . . , an}, {b0, . . . , bn}} and
Si = {{a0, bi}, {b0, ai}} for i = 1, . . . , n."

**Formalization Note** Players are `Fin (n+1)`: player `0` is the heavy player (weight `1`),
players `1, …, n` are the light players (weight `w`). Resources are `Fin ((n+1)+(n+1))`:
`aᵢ = Fin.castAdd (n+1) i` (indices `0, …, n`) and `bᵢ = Fin.natAdd (n+1) i` (indices
`n+1, …, 2n+1`). Weights must be positive (§2: `wᵢ > 0`), so `w : ℝ≥0` comes with `0 < w`; the
paper's family also allows `w = 0`, which is not a game. `β` is real; the theorems on the gadget
assume `β ∈ [0,1]`, `1 ≤ k ≤ d`, `w ≤ 1` as on p.4. -/
noncomputable def gadget (d n k : ℕ) (w : ℝ≥0) (hw : 0 < w) (β : ℝ) :
    Game (n + 1) ((n + 1) + (n + 1)) where
  players_pos := Nat.succ_pos n
  facilities_pos := by omega
  strategies := fun i =>
    if i = 0 then
      {Finset.univ.image (Fin.castAdd (n + 1)), Finset.univ.image (Fin.natAdd (n + 1))}
    else
      {{Fin.castAdd (n + 1) 0, Fin.natAdd (n + 1) i}, {Fin.natAdd (n + 1) 0, Fin.castAdd (n + 1) i}}
  strategies_nonempty := fun i => by
    split_ifs <;> exact Finset.insert_nonempty _ _
  demand := fun i => if i = 0 then 1 else w
  demand_pos := fun i => by
    split_ifs
    · exact one_pos
    · exact hw
  cost := fun f x =>
    if f = Fin.castAdd (n + 1) 0 ∨ f = Fin.natAdd (n + 1) 0 then (x : ℝ) ^ k
    else β * (x : ℝ) ^ d

end CongestionApproxPNE


