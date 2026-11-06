-- Prove2me | Definitions.Def_ConeL2G_leafGraph
-- name    : ConeL2G_leafGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:55.521637+00:00
-- url     : https://prove2.me/theorems/a233f2c9-6434-4ca8-9497-6f0a7e3082ea
-- title:
--   The leaf graph $H'$ (center at a dummy color)
-- statement:
--   For a cone $H=\{v\}\cup H'$, the leaf graph is the subgraph of $H$ induced on the leaves $V\setminus\{v\}$.
--
--   The paper's objects with "the center assigned a dummy color that does not belong to any of the leaf lists" — the uniform law $\mu^{-v}_{H'}$ on proper colorings of the leaves from $\prod_i L_i$ and the operators $D^{-v,H'}_i$, $\Pi^{-v,H'}_{i,c}$ — are the objects of this induced graph with the same lists: a dummy center color removes no color from any leaf. The degree of a leaf $i$ in this graph is $\deg_{H'}(i)$.
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Section 6, p.18

import Mathlib

namespace ConeL2G

/-- **The leaf graph** of a cone centered at `v`: the graph induced on the leaves
`H′ = V ∖ {v}`. Li–Oveis Gharan, arXiv:2610.37721, Section 6, p.18: "Let `µ^{−v}_{H′}` be the
uniform distribution on the proper colorings of leaves from `∏ᵢ Lᵢ` when we assume that the center
is assigned a dummy color that does not belong to any of the leaf lists … We further define the
operators `D^{−v,H′}` and `Π^{−v,H′}_{i,c}` acting on `L²(µ^{−v}_{H′})` to denote operators obtained
by pinning the center to the dummy color."

**Formalization Note.** A dummy center color lies in no leaf list, so it removes no color from any
leaf: the leaves with the center at a dummy color are exactly this induced graph with the same
lists `fun u => L u.1`. Hence `µ^{−v}_{H′} = ConeL2G.unifMass (leafGraph H v) (fun u => L u.1)`,
and `D^{−v,H′}_i`, `Π^{−v,H′}_{i,c}` are the operators of that graph. `deg_{H′}(i)` is the degree in
this graph. -/
def leafGraph {V : Type*} (H : SimpleGraph V) (v : V) : SimpleGraph {u : V // u ≠ v} :=
  H.comap Subtype.val

instance leafGraph.decidableAdj {V : Type*} (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) :
    DecidableRel (leafGraph H v).Adj :=
  fun a b => inferInstanceAs (Decidable (H.Adj a.1 b.1))

end ConeL2G


