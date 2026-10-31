-- Prove2me | Definitions.Def_CongestionApproxPNE_playerCost
-- name    : CongestionApproxPNE_playerCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:15:50.749181+00:00
-- url     : https://prove2.me/theorems/1b75bc67-0ba3-44ff-95e2-8c1254d74184
-- title:
--   Player cost $C_i(s)=\sum_{e\in s_i} c_e(x_e(s))$
-- statement:
--   Let $G$ be a weighted congestion game with players $N=\{1,\dots,n\}$, resources $E$, nondecreasing cost functions $c_e$, weights $w_i>0$ and strategy sets $S_i\subseteq 2^E$. For a strategy profile $s=(s_1,\dots,s_n)$ the **load** of resource $e$ is the total weight of the players using it, $x_e(s)=\sum_{i:\,e\in s_i} w_i$, and the **cost of player $i$** is
--
--   $$
--   C_i(s)=\sum_{e\in s_i} c_e\bigl(x_e(s)\bigr).
--   $$
--
--   The cost carries no weight factor: a heavy player pays the same per-resource latency as a light one, while her weight raises the load everyone on that resource sees. This is the quantity that the approximate-equilibrium condition (1) compares.
--
--   **Formalization Note** The game is the published `HarksKlimm.Consistency.Game n m` (players `Fin n`, resources `Fin m`, nonempty finite strategy sets, positive weights `demand` in $\mathbb R_{\ge 0}$) and the load is the published `HarksKlimm.Consistency.load`. The demand-weighted `HarksKlimm.Consistency.privateCost` is deliberately not used.
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, §2, p.3 (PDF p.4), definition of Ci(s) and xe(s)

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game
import Definitions.Def_HarksKlimm_Consistency_load

set_option autoImplicit false
open scoped NNReal

namespace CongestionApproxPNE

open HarksKlimm.Consistency

/-- **The cost of player `i` under profile `s`**, `C_i(s) = Σ_{e ∈ s_i} c_e(x_e(s))`.
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, *Existence and Complexity of Approximate
Equilibria in Weighted Congestion Games*, arXiv:2002.07466v3, §2, p.3: "Each strategy profile s
induces a cost of Ci(s) = Σ_{e∈si} ce(xe(s)) to every player i ∈ N, where xe(s) = Σ_{i:e∈si} wi is
the induced load on resource e."

**Formalization Note** The game is the published weighted congestion game
`HarksKlimm.Consistency.Game n m` (players `Fin n`, resources `Fin m`, weights `demand`), and the
load `x_e(s)` is the published `HarksKlimm.Consistency.load` (the sum of the weights of the players
using `e`). The player's cost carries **no** weight factor, as on p.3 (unlike the demand-weighted
`HarksKlimm.Consistency.privateCost`). -/
noncomputable def playerCost {n m : ℕ} (G : Game n m) (s : G.Profile) (i : Fin n) : ℝ :=
  ∑ f ∈ (s i).val, G.cost f (load G s f)

end CongestionApproxPNE


