-- Prove2me | Definitions.Def_ArcFlowBPP_FlowConservation
-- name    : ArcFlowBPP_FlowConservation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:55.993312+00:00
-- url     : https://prove2.me/theorems/c422d3de-56f4-4e2b-ad18-77ea8975613b
-- title:
--   Flow conservation (18) with value $z$
-- statement:
--   For a flow $f$ on the arcs and a value $z$, the **flow conservation constraints** (18) are, for every vertex $k$,
--
--   $$
--   \sum_{(u,v,i)\in A:\, v=k} f_{uvi} \;-\; \sum_{(v,r,i)\in A:\, v=k} f_{vri} \;=\; \begin{cases} -z & k = s,\\ z & k = t,\\ 0 & k \in V \setminus \{s,t\}. \end{cases}
--   $$
--
--   The inflow minus the outflow is $-z$ at the source, $z$ at the target and $0$ elsewhere.
--
--   **Formalization Note** The constraint is written without subtraction as $\mathrm{in}(k) + [k = s]\,z = \mathrm{out}(k) + [k = t]\,z$, so that it can be stated over $\mathbb N$ (integer program) as well as over $\mathbb R$ (linear relaxation). For $s \ne t$, which the standing assumptions imply, it is equivalent to (18).
-- source:
--   Brandão, Pedroso, Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression, arXiv:1310.6887v1, eq. (18), p.7

import Mathlib
import Definitions.Def_ArcFlowBPP_LabelledGraph

namespace ArcFlowBPP

/-- Brandão, Pedroso, *Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression*, arXiv:1310.6887v1, eq. (18), p.7: flow conservation with value `z`,
`∑_{(u,v,i)∈A : v=k} f_{uvi} − ∑_{(v,r,i)∈A : v=k} f_{vri} = −z if k = s, z if k = t, 0 for k ∈ V ∖ {s, t}`.

**Formalization Note.** To avoid subtraction (and truncated subtraction over `ℕ`) the display is
written as `inflow k + [k = s]·z = outflow k + [k = t]·z` for every vertex `k`. When `s ≠ t`
(which the standing assumption `ArcFlowBPP.IsArcFlowGraph` implies) this is equivalent to (18)
over `ℤ` and `ℝ`. The coefficient type `R` is `ℕ` for the integer program and `ℝ` for its linear
relaxation. -/
def FlowConservation {m : ℕ} {V A : Type*} [Fintype A] [DecidableEq V] {R : Type*}
    [AddCommMonoid R] (G : LabelledGraph m V A) (f : A → R) (z : R) : Prop :=
  ∀ k : V,
    (∑ a ∈ Finset.univ.filter (fun a => G.head a = k), f a) + (if k = G.s then z else 0) =
      (∑ a ∈ Finset.univ.filter (fun a => G.tail a = k), f a) + (if k = G.t then z else 0)

end ArcFlowBPP


