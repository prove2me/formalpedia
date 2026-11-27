-- Prove2me | Definitions.Def_IncentiveFinNet_Supplement_ResultingNetwork
-- name    : IncentiveFinNet_Supplement_ResultingNetwork
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:27:46.797278+00:00
-- url     : https://prove2.me/theorems/d3099da1-3431-47fe-be63-fd913caf049b
-- title:
--   Agent action and resulting network (Definition 4)
-- statement:
--   Let $(W,P)$ be a feasible point of a network setting, and let agent $i$ have permitted counterparties $J_i$. An **action** of agent $i$ is a family $(w'_{j}, p'_{j})_{j\in J_i}$ of proposed contract sizes and prices, one for each permitted counterparty. Each counterparty $j \in J_i$, $j\ne i$, responds as follows (Definition 4):
--
--   1. if the new contract $(w'_j,p'_j)$ raises $j$'s utility, $j$ accepts: $W'_{ij} = W'_{ji} = w'_j$, $P'_{ij} = p'_j$, $P'_{ji} = -p'_j$;
--   2. otherwise agent $i$ keeps the existing contract ($W'_{ij}=W_{ij}$, $P'_{ij} = P_{ij}$, and symmetrically) or cancels it ($W'_{ij}=W'_{ji}=P'_{ij}=P'_{ji}=0$).
--
--   Whether the proposal raises $j$'s utility is decided by comparing $g_j(W,P)$ with $g_j$ at the network in which only the contract between $i$ and $j$ is replaced by $(w'_j,p'_j)$. When $i \in J_i$, the self-investment $W'_{ii}$ takes the proposed value $w'_i$, the old value $W_{ii}$, or $0$, and its price is unchanged. All entries not involving $i$, and the entries between $i$ and its prohibited counterparties, are unchanged. Any $(W',P')$ obtained in this way is a **resulting network** of the action.
--
--   Resulting networks are the unilateral deviations against which the Nash clause of Higher-Order Nash Stability (Definition 5) is tested.
--
--   **Formalization Note** The paper fixes the choice for a rejected proposal ("$i$ cancels the contract if and only if this strictly increases $i$'s utility"). Here both keeping and cancelling are allowed, whatever $i$ prefers, so every network produced by the paper's rule is a resulting network in this sense. The action is given by two functions on all agents, of which only the values on $J_i$ are used. Agent $j$'s utility depends only on column $j$ of $(W',P')$, and that column differs from $(W,P)$ only at the entry $(i,j)$, so the acceptance test is the same as evaluating $g_j$ in the resulting network.
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, Definition 4 (Agent Action), pp.12–13

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_IncentiveFinNet_Stable

open Matrix

namespace IncentiveFinNet.Supplement

/-- The network obtained from `(W, P)` by replacing the contract between `i` and `j` by size `w`
and price `p` (`W_ij = W_ji = w`, `P_ij = p`, `P_ji = −p`), all other entries unchanged. It is the
network at which agent `j` evaluates agent `i`'s proposal in Definition 4 (arXiv:2212.06808v3,
p.12). -/
def replaceEdge {n : ℕ} (W P : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (w p : ℝ) :
    Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.of fun a b => if (a = i ∧ b = j) ∨ (a = j ∧ b = i) then w else W a b,
   Matrix.of fun a b => if a = i ∧ b = j then p else if a = j ∧ b = i then -p else P a b)

/-- **Definition 4 (Agent Action)** and the resulting network, Jalan, Chakrabarti, Sarkar,
arXiv:2212.06808v3, pp.12–13: "At a given feasible point `(W, P)`, an 'action' by agent `i` is the
ordered set `(w′_{i,j}, p′_{i,j})_{j ∈ J_i}` […] Each agent `j ∈ J_i` responds as follows:
1. If the new `(w′_ij, p′_ij)` raises `j`'s utility, then `j` agrees to the revised contract and
price. 2. Otherwise, `i` must either keep the existing contract or cancel it (`w_ij = p_ij = 0`).
We assume that `i` cancels the contract if and only if this strictly increases `i`'s utility. We
call the shifted `(W′, P′)` the resulting network."

`ResultingNetwork S W P i w' p' W' P'` says that `(W′, P′)` is a resulting network of the action
`(w′ j, p′ j)_{j ∈ J_i}` of agent `i` at `(W, P)`:
* entries not involving `i`, and entries `(i, j)`, `(j, i)` with `j ∉ J_i`, are unchanged;
* for `j ∈ J_i`, `j ≠ i`: if `g_j` at `replaceEdge W P i j (w′ j) (p′ j)` is strictly larger than
  `g_j(W, P)`, the contract and price take the proposed values; otherwise the edge is kept (all four
  entries unchanged) or cancelled (all four entries `0`);
* the self-loop `(i, i)` (only if `i ∈ J_i`) takes the proposed size `w′ i`, is kept, or is
  cancelled; its price is unchanged.

**Formalization Note**
* The action is given by functions `w′ p′ : Fin n → ℝ`; only their values on `J_i` are used.
* For a rejected proposal the definition allows both "keep" and "cancel", whatever `i` prefers. The
  paper fixes the choice ("cancel iff this strictly increases `i`'s utility"); every network the
  paper's rule produces is a resulting network here.
* `j`'s utility depends only on column `j`, and in the resulting network that column differs from
  `(W, P)` only in the entry `(i, j)`, so evaluating the proposal at `replaceEdge` is evaluating it
  in the resulting network. -/
def ResultingNetwork {n : ℕ} (S : NetworkSetting n) (W P : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (w' p' : Fin n → ℝ) (W' P' : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ a b, a ≠ i → b ≠ i → W' a b = W a b ∧ P' a b = P a b) ∧
  (∀ j, j ∉ S.J i → W' i j = W i j ∧ W' j i = W j i ∧ P' i j = P i j ∧ P' j i = P j i) ∧
  (∀ j, j ∈ S.J i → j ≠ i →
    (S.utility j W P < S.utility j (replaceEdge W P i j (w' j) (p' j)).1
        (replaceEdge W P i j (w' j) (p' j)).2 →
      W' i j = w' j ∧ W' j i = w' j ∧ P' i j = p' j ∧ P' j i = -p' j) ∧
    (¬ S.utility j W P < S.utility j (replaceEdge W P i j (w' j) (p' j)).1
        (replaceEdge W P i j (w' j) (p' j)).2 →
      (W' i j = W i j ∧ W' j i = W j i ∧ P' i j = P i j ∧ P' j i = P j i) ∨
      (W' i j = 0 ∧ W' j i = 0 ∧ P' i j = 0 ∧ P' j i = 0))) ∧
  (i ∈ S.J i → (W' i i = w' i ∨ W' i i = W i i ∨ W' i i = 0) ∧ P' i i = P i i)

end IncentiveFinNet.Supplement


