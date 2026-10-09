-- Prove2me | Definitions.Def_AggGameNet_GossipConst_Game
-- name    : AggGameNet_GossipConst_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:30:48.327523+00:00
-- url     : https://prove2.me/theorems/25885657-249c-442f-a974-723f3abbb3ec
-- title:
--   §2 game, variational inequality, and assumptions
-- statement:
--   Let $N\ge1$ players choose vectors $x_i$ in nonempty compact convex sets $K_i\subseteq\mathbb R^n$. The feasible profile set is $K=\prod_i K_i$, and its aggregate set is $\bar K=\{\sum_i x_i:x_i\in K_i\}$. Given component maps $F_i$, define $\phi(x)_i=F_i(x_i,\sum_j x_j)$. A profile $x^*\in K$ solves $\operatorname{VI}(K,\phi)$ when
--
--   $$\sum_i\langle x_i-x_i^*,\phi(x^*)_i\rangle\ge0\qquad(x\in K).$$
--
--   The file also defines Assumption 1 as compact convex strategy sets and continuity of $F_i$ on $K_i\times\bar K$; Assumption 3 as Lipschitz continuity in the aggregate with positive constants $\bar L_i$; Assumption 8 as Lipschitz continuity in the decision at fixed aggregate with positive constants $L_i$; strong monotonicity with modulus $\mu$; and Euclidean nearest-point projection as a relation. These objects are the common interface for the paper's gossip result.
--
--   **Formalization Note** The paper's differentiable payoff functions $f_i$ are represented through their gradient components $F_i$, the only maps used by this algorithm. Continuity of $F_i$ is the part of Assumption 1 needed here. Assumption 3 applies to all aggregate arguments in $\mathbb R^n$, rather than only $\bar K$, because the algorithm evaluates $F_i$ at $N\hat v_i^k$, which may lie outside $\bar K$ (p. 10, footnote 4).
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, (1)–(8), Assumptions 1 and 3, pp. 4–7; Assumption 8 and strong monotonicity, p. 26

import Mathlib
import Definitions.Def_AggGameNet_Gossip_Setting
import Definitions.Def_AggGameNet_Sync_Game
import Definitions.Def_AggGameNet_Sync_Setting

namespace AggGameNet.GossipConst

def Assumption8 {N n : ℕ} (K : Fin N → Set (AggGameNet.Sync.E n))
    (F : Fin N → AggGameNet.Sync.E n → AggGameNet.Sync.E n → AggGameNet.Sync.E n) (L : Fin N → ℝ) : Prop :=
  (∀ i, 0 < L i) ∧
  ∀ i, ∀ u ∈ AggGameNet.Sync.Kbar K, ∀ a ∈ K i, ∀ b ∈ K i,
    ‖F i a u - F i b u‖ ≤ L i * ‖a - b‖

def StronglyMonotone {N n : ℕ} (K : Fin N → Set (AggGameNet.Sync.E n))
    (F : Fin N → AggGameNet.Sync.E n → AggGameNet.Sync.E n → AggGameNet.Sync.E n) (mu : ℝ) : Prop :=
  ∀ x y : Fin N → AggGameNet.Sync.E n, (∀ i, x i ∈ K i) → (∀ i, y i ∈ K i) →
    mu * ∑ i, ‖x i - y i‖ ^ 2 ≤
      ∑ i, inner ℝ (AggGameNet.Sync.phi F x i - AggGameNet.Sync.phi F y i) (x i - y i)

end AggGameNet.GossipConst


