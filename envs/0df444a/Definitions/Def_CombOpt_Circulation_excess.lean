-- Prove2me | Definitions.Def_CombOpt_Circulation_excess
-- name    : CombOpt_Circulation_excess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:08.605293+00:00
-- url     : https://prove2.me/theorems/ad85570b-1c4a-48aa-bf45-13722dd59355
-- title:
--   Net flow into a node $f_x(v)$
-- statement:
--   For $x\in\mathbb R^E$ and a node $v$, the **net flow into** $v$, or **excess** of $x$ at $v$, is
--
--   $$
--   f_x(v)=\sum_{w\in V,\ wv\in E}x_{wv}-\sum_{w\in V,\ vw\in E}x_{vw}.
--   $$
--
--   The conservation constraints of flows, circulations and transshipment systems are all conditions on $f_x$.
--
--   **Formalization Note** The sums range over arcs with head $v$ and over arcs with tail $v$, so a loop at $v$ occurs in both and cancels.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §3.2, (3.1), p. 38 (PDF p. 47)

import Mathlib
import Definitions.Def_CombOpt_Circulation_MultiDigraph

namespace CombOpt.Circulation

variable {V E : Type*} [Fintype E] [DecidableEq V]

/-- The net flow into `v`, or excess of `x` at `v`,
`f_x(v) = ∑(x_wv : w ∈ V, wv ∈ E) − ∑(x_vw : w ∈ V, vw ∈ E)` of Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §3.2, left-hand side of (3.1),
p. 38 (PDF p. 47).

**Formalization Note** A loop at `v` occurs in both sums and cancels. -/
noncomputable def excess (G : MultiDigraph V E) (x : E → ℝ) (v : V) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e => G.head e = v), x e -
    ∑ e ∈ Finset.univ.filter (fun e => G.tail e = v), x e

end CombOpt.Circulation


