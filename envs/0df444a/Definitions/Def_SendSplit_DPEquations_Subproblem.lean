-- Prove2me | Definitions.Def_SendSplit_DPEquations_Subproblem
-- name    : SendSplit_DPEquations_Subproblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:13:13.629978+00:00
-- url     : https://prove2.me/theorems/74d490a5-1cda-437d-8f9c-7ede24d850d2
-- title:
--   Section 3 — demand nodes D, r_I, the subproblem i → I and its minimum cost C_iI (+∞ if it has no flow)
-- statement:
--   In the network model of Section 2, let $D = \{ i \in N : r_i \neq 0 \}$ be the set of **demand nodes**. The send-and-split equations are indexed by the sets $I$ with $\emptyset \subset I \subseteq D$ (nonempty subsets of $D$, $I = D$ allowed); for such $I$ write $r_I = \sum_{j \in I} r_j$.
--
--   For a node $i \in N$ and a set $I \subseteq N$, the **subproblem** $i \to I$ is obtained from the original problem by first replacing $r_j$ by zero for all $j \in N \setminus I$ and then subtracting $r_I$ from the resulting demand at node $i$. Its demand vector is therefore
--
--   $$r^{iI}_k \;=\; \mathbf{1}[k \in I]\, r_k \;-\; \mathbf{1}[k = i]\, r_I , \qquad k \in N .$$
--
--   The value $C_{iI}$ is the **minimum cost among all flows for the subproblem** $i \to I$:
--
--   $$C_{iI} \;=\; \inf \{ c(x) : x \text{ a flow for } r^{iI} \} \in \mathbb{R} \cup \{\pm\infty\},$$
--
--   with $C_{iI} = +\infty$ when the subproblem has no flow, as on p. 640.
--
--   The quantities $C_{iI}$ are the unknowns of the dynamic-programming equations (1)–(3); Theorem 2 characterizes them as the greatest solution of those equations.
--
--   **Formalization Note** $C_{iI}$ is an `EReal` infimum, so the empty infimum is $+\infty$ (`⊤`), matching the page. That the infimum is attained and never $-\infty$ under the hypothesis of Theorem 2 is not built into the definition; it is the milestone *subproblem attainment*. The definition makes sense for every $i$ and $I$; the equations only use $\emptyset \subset I \subseteq D$ (`IsAdmissible`).
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), p. 638 (demand nodes) and p. 640, Section 3

import Mathlib
import Definitions.Def_SendSplit_DPEquations_Network

namespace SendSplit.DPEquations

/-- The demand nodes `D = {i : r_i ≠ 0}` (p. 638). -/
noncomputable def demandNodes {n : ℕ} (r : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => r i ≠ 0)

/-- The index sets of the send-and-split equations: `∅ ⊂ I ⊆ D`. -/
def IsAdmissible {n : ℕ} (r : Fin n → ℝ) (I : Finset (Fin n)) : Prop :=
  I.Nonempty ∧ I ⊆ demandNodes r

/-- `r_I ≡ Σ_{j ∈ I} r_j` (p. 640). -/
def demandSum {n : ℕ} (r : Fin n → ℝ) (I : Finset (Fin n)) : ℝ :=
  ∑ j ∈ I, r j

/-- The demand vector of the subproblem `i → I` (p. 640): replace `r_j` by zero for all
`j ∉ I`, then subtract `r_I` from the resulting demand at node `i`. -/
def subDemand {n : ℕ} (r : Fin n → ℝ) (i : Fin n) (I : Finset (Fin n)) : Fin n → ℝ :=
  fun k => (if k ∈ I then r k else 0) - (if k = i then demandSum r I else 0)

/-- `C_iI` (p. 640): the minimum cost among all flows for the subproblem `i → I`, as an
extended real; it is `+∞` (the empty infimum) when the subproblem has no flow. -/
noncomputable def minCost {n : ℕ} (A : Finset (Fin n × Fin n)) (c : Fin n → Fin n → ℝ → ℝ)
    (r : Fin n → ℝ) (i : Fin n) (I : Finset (Fin n)) : EReal :=
  ⨅ (x : Fin n → Fin n → ℝ) (_ : IsFlow A (subDemand r i I) x), ((flowCost A c x : ℝ) : EReal)

end SendSplit.DPEquations


