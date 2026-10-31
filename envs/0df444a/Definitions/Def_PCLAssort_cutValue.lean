-- Prove2me | Definitions.Def_PCLAssort_cutValue
-- name    : PCLAssort_cutValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:16:53.764479+00:00
-- url     : https://prove2.me/theorems/28d15a67-7f0c-47b7-a2c8-a69a96d53b1d
-- title:
--   Value of a directed cut
-- statement:
--   Let $(V,E)$ be a directed graph with edge weights $w:E\to\mathbb R$. For a vertex set $T\subseteq V$, the value of the directed cut defined by $T$ is the total weight of the edges leaving $T$:
--
--   $$
--   \mathrm{cut}(T)=\sum_{(i,j)\in E:\ i\in T,\ j\notin T} w_{ij}.
--   $$
--
--   The maximum directed cut problem (max-dicut) asks for a set $T$ maximizing this value, possibly subject to constraints on $T$.
--
--   **Formalization Note** $V$ is a finite type, $E$ a finite set of ordered pairs, and $w$ is given on all ordered pairs; only its values on $E$ matter.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), Definition 1, p.790 (PDF p.6)

import Mathlib

namespace PCLAssort

/-- Value of a directed cut (Definition 1, Maximum Directed Cut, Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.790): for a directed
graph `(V, E)` with edge weights `w`, the total weight of the edges leaving the vertex set `T`,
`∑_{(i,j) ∈ E : i ∈ T, j ∉ T} w_ij`. Max-dicut maximizes this over `T ⊆ V`.

**Formalization Note.** The edge set is a `Finset (V × V)` of ordered pairs and `w` is a weight
function on all ordered pairs, of which only the values on `E` matter. -/
def cutValue {V : Type} [DecidableEq V] (E : Finset (V × V)) (w : V × V → ℝ) (T : Finset V) : ℝ :=
  ∑ e ∈ E.filter (fun e => e.1 ∈ T ∧ e.2 ∉ T), w e

end PCLAssort


