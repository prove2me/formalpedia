-- Prove2me | Definitions.Def_CombOpt_TJoin_Graph_IsFeasible533
-- name    : CombOpt_TJoin_Graph_IsFeasible533
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:22.155987+00:00
-- url     : https://prove2.me/theorems/5d3a8392-9569-4b1b-844d-8774345664cd
-- title:
--   Feasible solutions of the $T$-cut LP (5.33)
-- statement:
--   A set $S\subseteq V$ is **$T$-odd** if $|S\cap T|$ is odd, and then $\delta(S)$ is a **$T$-cut**. A vector $x\in\mathbb R^E$ is feasible for the linear program
--
--   $$\text{minimize } \sum_{e\in E}c_ex_e \quad\text{subject to}\quad x(D)\ge1 \text{ for all } T\text{-cuts } D,\qquad x_e\ge0 \text{ for all } e\in E \tag{5.33}$$
--
--   if it satisfies these constraints.
--
--   **Formalization Note** The $T$-cuts are listed through the $T$-odd sets $S$; a cut arising from several sets is the same constraint repeated.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.4, (5.33), p. 178 (PDF p. 186)

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph
import Definitions.Def_CombOpt_TJoin_Graph_cut

namespace CombOpt.TJoin

/-- **Feasible solutions of the T-cut linear program (5.33).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.4, p. 178 (PDF p. 186): "A set S ⊆ V is T-odd if |S ∩ T| is odd. In this case δ(S) is
called a T-cut." and
"Minimize ∑(c_e x_e : e ∈ E) (5.33) subject to x(D) ≥ 1, for all T-cuts D; x_e ≥ 0, for all
e ∈ E."

`G.IsFeasible533 T x` holds when `x(δ(S)) ≥ 1` for every `S ⊆ V` with `|S ∩ T|` odd, and `x ≥ 0`.

**Formalization Note.** The T-cuts are listed through the T-odd sets `S` that define them; a cut
arising from several sets is the same constraint repeated. -/
def Graph.IsFeasible533 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] (G : Graph V E)
    (T : Finset V) (x : E → ℝ) : Prop :=
  (∀ S : Finset V, Odd (S ∩ T).card → 1 ≤ ∑ e ∈ G.cut S, x e) ∧ ∀ e, 0 ≤ x e

end CombOpt.TJoin


