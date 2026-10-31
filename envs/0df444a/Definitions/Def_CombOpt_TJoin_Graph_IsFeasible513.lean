-- Prove2me | Definitions.Def_CombOpt_TJoin_Graph_IsFeasible513
-- name    : CombOpt_TJoin_Graph_IsFeasible513
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:16.193685+00:00
-- url     : https://prove2.me/theorems/a76c11f6-28df-4b41-8c40-95c6273d2adf
-- title:
--   Feasible solutions of Edmonds' perfect-matching LP (5.13)
-- statement:
--   A cut $D$ is **odd** if $D=\delta(S)$ for some $S\subseteq V$ with $|S|$ odd; $\mathcal C$ is the set of odd cuts not of the form $\delta(v)$ for a node $v$. A vector $x\in\mathbb R^E$ is feasible for
--
--   $$\text{minimize } \sum_{e\in E}c_ex_e \tag{5.13}$$
--
--   subject to
--
--   $$x(\delta(v))=1 \ (v\in V),\qquad x(D)\ge1\ (D\in\mathcal C),\qquad x_e\ge0\ (e\in E) \tag{5.14–5.16}$$
--
--   if it satisfies (5.14)–(5.16).
--
--   **Formalization Note** The members of $\mathcal C$ are listed through the odd sets $S$ whose cut differs from every $\delta(v)$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.3, (5.13)–(5.16), pp. 147–148 (PDF pp. 155–156)

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph
import Definitions.Def_CombOpt_TJoin_Graph_cut

namespace CombOpt.TJoin

/-- **Feasible solutions of Edmonds' perfect-matching linear program (5.13)–(5.16).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.3, p. 147–148 (PDF pp. 155–156): "We call a cut D of G odd if it is of the form δ(S)
where S is an odd-cardinality set of nodes. … Let C denote the set of all odd cuts of G that are
not of the form δ(v) for some node v." and
"Minimize ∑(c_e x_e : e ∈ E) (5.13) subject to x(δ(v)) = 1, for all v ∈ V (5.14);
x(D) ≥ 1, for all D ∈ C (5.15); x_e ≥ 0, for all e ∈ E (5.16)."

`G.IsFeasible513 x` holds when `x(δ(v)) = 1` for every node, `x(δ(S)) ≥ 1` for every
odd-cardinality `S` whose cut differs from every star `δ(v)`, and `x ≥ 0`.

**Formalization Note.** The members of `C` are listed through the odd sets `S` that define them;
a cut arising from several sets is the same constraint repeated. -/
def Graph.IsFeasible513 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] (G : Graph V E)
    (x : E → ℝ) : Prop :=
  (∀ v : V, ∑ e ∈ G.cut {v}, x e = 1) ∧
    (∀ S : Finset V, Odd S.card → (∀ v : V, G.cut S ≠ G.cut {v}) → 1 ≤ ∑ e ∈ G.cut S, x e) ∧
    ∀ e, 0 ≤ x e

end CombOpt.TJoin


