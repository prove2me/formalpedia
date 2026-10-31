-- Prove2me | Definitions.Def_CombOpt_HeldKarp_Graph_InsideFeasible
-- name    : CombOpt_HeldKarp_Graph_InsideFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:07:44.99541+00:00
-- url     : https://prove2.me/theorems/7785bdc8-d7a4-4712-8451-9d684bf02d54
-- title:
--   Feasibility for the inside form (7.2)–(7.6)
-- statement:
--   Fix a node $v_1$. A vector $x\in\mathbb R^E$ satisfies the **inside form** of the subtour LP if
--
--   1. $x(\delta(v))=2$ for all $v\in V$ (7.3);
--   2. $x(\gamma(S))\le |S|-1$ for all nonempty $S\subseteq V$ with $v_1\notin S$ (7.4);
--   3. $x(\gamma(V\setminus\{v_1\}))=|V|-2$ (7.5);
--   4. $0\le x_e\le 1$ for all $e\in E$ (7.6).
--
--   **Formalization Note** The book prints (7.4) for all $S\subseteq V$ with $v_1\notin S$; at $S=\emptyset$ it reads $0\le -1$, so $S$ is required nonempty here (the inside form of $x(\delta(S))\ge2$, $\emptyset\ne S\ne V$). The correction is recorded on the theorems using this definition.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §7.3, (7.2)–(7.6), p. 259 (PDF p. 267)

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph_cut
import Definitions.Def_CombOpt_HeldKarp_Graph_gamma

namespace CombOpt.HeldKarp

/-- **x satisfies the "inside" form (7.3)–(7.6) of the subtour constraints.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §7.3, (7.2),
p. 259 (PDF p. 267): "Minimize Σ(c_e x_e : e ∈ E) (7.2) subject to x(δ(v)) = 2, for all v ∈ V
(7.3); x(γ(S)) ≤ |S| − 1, for all S ⊆ V, v_1 ∉ S (7.4); x(γ(V \ {v_1})) = |V| − 2 (7.5);
0 ≤ x_e ≤ 1, for all e ∈ E (7.6)."

`G.InsideFeasible v₁ x` is the conjunction of (7.3)–(7.6), with (7.4) imposed for every **nonempty**
`S ⊆ V` with `v₁ ∉ S`.

**Formalization Note.** The page prints (7.4) for all `S ⊆ V` with `v₁ ∉ S`, which includes `S = ∅`
and then reads `0 ≤ −1`, making (7.2) infeasible always; the inside form of the subtour constraint
`x(δ(S)) ≥ 2` for `∅ ≠ S ≠ V` concerns nonempty `S` only, so `S` is required nonempty (a correction,
recorded on the theorems that use it). `|S| − 1` and `|V| − 2` are computed in `ℝ`. -/
def Graph.InsideFeasible {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (G : Graph V E)
    (v₁ : V) (x : E → ℝ) : Prop :=
  (∀ v : V, ∑ e ∈ G.cut {v}, x e = 2) ∧
  (∀ S : Finset V, S.Nonempty → v₁ ∉ S → ∑ e ∈ G.gamma S, x e ≤ (S.card : ℝ) - 1) ∧
  (∑ e ∈ G.gamma (Finset.univ.erase v₁), x e = (Fintype.card V : ℝ) - 2) ∧
  (∀ e : E, 0 ≤ x e ∧ x e ≤ 1)

end CombOpt.HeldKarp


