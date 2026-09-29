-- Prove2me | Definitions.Def_OptimumBranchings_Polytope_DualCertificate
-- name    : OptimumBranchings_Polytope_DualCertificate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:52:31.039373+00:00
-- url     : https://prove2.me/theorems/22f009de-4150-422f-886f-71075db57711
-- title:
--   The dual of $(L_1)$–$(L_3)$ and the certificate conditions (15)–(20) (§6)
-- statement:
--   Let $G$ be a directed graph with nodes $V$, edges $E$, and real edge weights $c=(c_e)$. The dual variables are a number $y_h$ for every node $v_h$ and a number $y_S$ for every set $S$ of two or more nodes. For an edge $e$ put
--   $$
--   w_e=\sum_{S:\ |S|\ge 2,\ \mathrm{front}(e)\in S,\ \mathrm{rear}(e)\in S} y_S ,
--   $$
--   and let the dual objective be $(b,y)=\sum_h y_h+\sum_{S:\,|S|\ge2}(|S|-1)\,y_S$.
--
--   The vector $y$ is **dual feasible** if
--
--   1. (15) $y_h\ge 0$ for every node $v_h$;
--   2. (16) $y_S\ge 0$ for every set $S$ with $|S|\ge 2$;
--   3. (17) $y_h+w_e\ge c_e$ for every edge $e$, where $v_h$ is the front end of $e$.
--
--   For a set of edges $B$ with incidence vector $x^0$, $y$ is a **dual certificate** for $B$ if it is dual feasible and moreover
--
--   4. (18) for every node $v_h$ with $y_h\ne 0$, $\sum_{e:\ \mathrm{front}(e)=v_h}x^0_e=1$;
--   5. (19) for every set $S$ with $|S|\ge2$ and $y_S\ne0$, $\sum_{e:\ \text{both ends in }S}x^0_e=|S|-1$;
--   6. (20) for every edge $e\in B$, $y_h+w_e=c_e$, where $v_h$ is the front end of $e$.
--
--   Conditions (18)–(20) are the complementary slackness conditions of linear programming for the system $(L_1)$–$(L_3)$ and its dual; Edmonds' proof of optimality consists in producing such a certificate.
--
--   **Formalization Note** The set variables are a function `Finset V → ℝ`; its values on sets with fewer than two nodes are ignored by every condition and by $w_e$ and $(b,y)$.
-- source:
--   Edmonds, Optimum branchings, J. Res. Nat. Bur. Standards 71B (1967), pp. 236–237, Section 6, (15)–(20)

import Mathlib
import Definitions.Def_OptimumBranchings_Polytope_Graph

namespace OptimumBranchings.Polytope

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- `w_e = ∑ y_S`, summed over all sets `S` of two or more nodes which contain both ends of the
edge `e` (§6, (17), p. 237). Values of `ySet` on sets with fewer than two nodes are ignored. -/
def edgeSetDual (G : Graph V E) (ySet : Finset V → ℝ) (e : E) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset V => 2 ≤ S.card ∧ G.front e ∈ S ∧ G.rear e ∈ S),
    ySet S

/-- Dual feasibility (§6, (15)–(17), pp. 236–237) for the edge weights `c`: a variable
`yNode v` for each node and `ySet S` for each set `S` of two or more nodes, with
(15) `yNode v ≥ 0`, (16) `ySet S ≥ 0` for `|S| ≥ 2`, and (17) for every edge `e`,
`yNode (front e) + w_e ≥ c e`. -/
def IsDualFeasible (G : Graph V E) (c : E → ℝ) (yNode : V → ℝ) (ySet : Finset V → ℝ) : Prop :=
  (∀ v, 0 ≤ yNode v) ∧
  (∀ S : Finset V, 2 ≤ S.card → 0 ≤ ySet S) ∧
  (∀ e, c e ≤ yNode (G.front e) + edgeSetDual G ySet e)

/-- The dual objective `(b, y) = ∑_h y_h + ∑_S (|S| - 1) y_S`, summed over all nodes and over
all sets `S` of two or more nodes (§6, p. 237). -/
def dualObjective (yNode : V → ℝ) (ySet : Finset V → ℝ) : ℝ :=
  ∑ v, yNode v + ∑ S ∈ Finset.univ.filter (fun S : Finset V => 2 ≤ S.card),
    ((S.card : ℝ) - 1) * ySet S

/-- `(yNode, ySet)` is a dual certificate for the branching `B` and weights `c` (§6, (15)–(20),
pp. 236–237), with `x⁰` the incidence vector of `B`: dual feasibility (15)–(17), and
(18) every node `v` with `yNode v ≠ 0` has `∑ x⁰_e = 1` over the edges directed toward `v`;
(19) every set `S` of two or more nodes with `ySet S ≠ 0` has `∑ x⁰_e = |S| - 1` over the edges
with both ends in `S`; (20) every edge `e` of `B` has `yNode (front e) + w_e = c e`. -/
def IsDualCertificate (G : Graph V E) (c : E → ℝ) (B : Finset E)
    (yNode : V → ℝ) (ySet : Finset V → ℝ) : Prop :=
  IsDualFeasible G c yNode ySet ∧
  (∀ v, yNode v ≠ 0 →
    ∑ e ∈ Finset.univ.filter (fun e => G.front e = v), incidenceVector B e = 1) ∧
  (∀ S : Finset V, 2 ≤ S.card → ySet S ≠ 0 →
    ∑ e ∈ Finset.univ.filter (fun e => G.front e ∈ S ∧ G.rear e ∈ S), incidenceVector B e
      = (S.card : ℝ) - 1) ∧
  (∀ e ∈ B, yNode (G.front e) + edgeSetDual G ySet e = c e)

end OptimumBranchings.Polytope


