-- Prove2me | Definitions.Def_LubyMIS_Derandomized_Basic
-- name    : LubyMIS_Derandomized_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T22:53:41.397788+00:00
-- url     : https://prove2.me/theorems/a463e4a7-030c-4dd7-9b72-0a500cd7ec59
-- title:
--   Neighbourhood N(W), eliminated edges, sum(i) and Algorithm B's select step (§3.1–3.4)
-- statement:
--   Let $G' = (V', E')$ be the current graph of the MIS algorithm, a finite simple graph, and write $d(i)$ for the degree of a vertex $i$ and $\mathrm{adj}(i)$ for its set of neighbours.
--
--   1. **Neighbourhood.** For $W \subseteq V'$, $N(W) = \{ i \in V' : \exists j \in W,\ (i,j) \in E' \}$.
--   2. **Eliminated edges.** For a selected set $I' \subseteq V'$, the next current graph is the subgraph induced on $V' - (I' \cup N(I'))$. The number of edges eliminated by the round is the number of edges of $G'$ with at least one endpoint in $I' \cup N(I')$:
--   $$Y_k - Y_{k+1} = \bigl|\{ \{i,j\} \in E' : i \in I' \cup N(I') \text{ or } j \in I' \cup N(I') \}\bigr|.$$
--   3. **sum(i).** $\mathrm{sum}(i) = \sum_{j \in \mathrm{adj}(i)} 1/d(j)$.
--   4. **Algorithm B's select step.** Given coin values $\mathrm{coin}(i) \in \{0,1\}$, let $X = \{ i : \mathrm{coin}(i) = 1 \}$ and start with $I' = X$. For every edge $(i,j)$ with both endpoints in $X$, in both orientations, the endpoint of smaller degree is removed, and on a tie in degree both are removed. Hence
--   $$I' = \{ i \in X : d(j) < d(i) \text{ for every } j \in \mathrm{adj}(i) \cap X \}.$$
--
--   These are the objects in terms of which Lemmas C and D and Theorems 2 and 3 are stated, and in terms of which Algorithm D's loop body is described.
--
--   **Formalization Note** The current graph is a `SimpleGraph` on a finite vertex type, taken as all of $V'$. The page defines $\mathrm{sum}(i)$ only when $d(i) \ge 1$; the Lean definition returns the empty sum $0$ at $d(i) = 0$. The printed select step of Algorithm B (p. 1040) does not initialize $I'$; Algorithm D's code (p. 1047) has $I' \leftarrow X$, which is used here. These four definitions are identical, body for body, to the ones of the companion mission on Algorithms A and B.
-- source:
--   Luby, A Simple Parallel Algorithm for the Maximal Independent Set Problem, SIAM J. Comput. 15(4), 1986, pp. 1038–1041, §3.1 (N(W)), §3.3 (select step of Algorithm B), §3.4 (Y_k, sum(i)); p. 1047 (I′ ← X)

import Mathlib

namespace LubyMIS.Derandomized

open Finset

/-- The neighbourhood `N(W) = {i ∈ V′ : ∃ j ∈ W, (i, j) ∈ E′}` of a vertex set `W` in the current
graph `H = G′` (Luby 1986, §3.1, p. 1038). -/
def nbhd {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (W : Finset V) :
    Finset V :=
  Finset.univ.filter (fun i => ∃ j ∈ W, H.Adj i j)

open Classical in
/-- The number of edges eliminated by one execution of the loop body that selects `I′`: the edges of
`H` with at least one endpoint in `Y = I′ ∪ N(I′)`. The induced subgraph on `V′ − Y` keeps exactly the
other edges, so this is `Y_k − Y_{k+1}` (§3.1, p. 1039; §3.4, p. 1040). -/
noncomputable def eliminated {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (I' : Finset V) : ℕ :=
  (H.edgeFinset.filter (fun e => ∃ v ∈ e, v ∈ I' ∪ nbhd H I')).card

/-- `sum(i) = ∑_{j ∈ adj(i)} 1 / d(j)` (§3.4, p. 1041). The page defines it only for `d(i) ≥ 1`; at
`d(i) = 0` this is the empty sum `0`. -/
noncomputable def sumInv {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (i : V) : ℝ :=
  ∑ j ∈ H.neighborFinset i, 1 / (H.degree j : ℝ)

/-- Algorithm B's select step (§3.3, p. 1040) for the coin values `c` (`X = {i : c i = true}`,
`I′` starting at `X`): `i ∈ X` survives iff every neighbour `j ∈ X` has `d(j) < d(i)`. -/
def selectB {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (c : V → Bool) :
    Finset V :=
  Finset.univ.filter (fun i => c i = true ∧ ∀ j, H.Adj i j → c j = true → H.degree j < H.degree i)

end LubyMIS.Derandomized


