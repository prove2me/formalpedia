-- Prove2me | Definitions.Def_TreeCoverLB_EJoin
-- name    : TreeCoverLB_EJoin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:53.065559+00:00
-- url     : https://prove2.me/theorems/8ac60da5-17a7-45c6-93eb-1a3ff0e59163
-- title:
--   The join $E_dG=(D(G))^{*(d+1)}$ and the layerwise action
-- statement:
--   For a finite group $G$ and $d\ge 0$, $E_dG=(D(G))^{*(d+1)}$ is the $(d+1)$-fold join of the discrete complex on $G$. Its vertices are the pairs $(i,g)$ with $i$ one of the $d+1$ layers and $g\in G$; a set of vertices is a face iff it contains at most one vertex in each layer. Its dimension is at most $d$.
--
--   $G$ acts on the vertices layerwise, $g\cdot(i,h)=(i,g+h)$, and hence on $|E_dG|\subseteq\mathbb R^{[d+1]\times G}$ by $(g\cdot\mu)(i,h)=\mu(i,-g+h)$.
--
--   **Formalization Note** Faces are the finite sets of vertices on which the layer map is injective. The group is written additively; for $G=\mathbb Z_p$ the action is the paper's $g(i,h)=(i,g+h)$, and on the cone $C_r$ it is the paper's $\gamma^a$ (§4.1).
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), §3.3, p.9 (PDF p.11) (E_dG); §4, p.11 (PDF p.13) (the action g(i, h) = (i, g + h))

import Mathlib
import Definitions.Def_TreeCoverLB_realization

open Classical

namespace TreeCoverLB

/-- The complex `E_dG = (D(G))^{∗(d+1)}`, the `(d+1)`-fold join of the discrete complex on a
finite group `G` (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), §3.3, p.9 (PDF p.11)): its vertices are the pairs `(i, g)` with `i` one of
the `d + 1` layers, and a face contains at most one vertex in each layer.

**Formalization Note** Vertices are `Fin (d+1) × G`; a finset is a face iff the layer map
`Prod.fst` is injective on it. -/
def EJoin (d : ℕ) (G : Type*) : Set (Finset (Fin (d + 1) × G)) :=
  {σ | Set.InjOn Prod.fst (σ : Set (Fin (d + 1) × G))}

/-- The action of `G` on `|E_dG|` induced by the layerwise action `g · (i, h) = (i, g + h)` on
vertices (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), §4, p.11 (PDF p.13): "g(i, h) = (i, g + h)"; the product action of §3.4 on the
general group `G`): `(g · µ)(i, h) = µ(i, −g + h)`.

**Formalization Note** The group is written additively (an `AddGroup`, not necessarily
commutative); for `G = ℤ_p` (`ZMod p`) this is literally the paper's `g(i, h) = (i, g + h)`.
The formula is the linear extension `Σ µ_{(i,h)} e_{(i, g+h)}` to all of `ℝ^{Fin (d+1) × G}`;
for `G = ℤ_p` it is also the action `γ^a` on the cone `C_r` (§4.1, p.12). -/
def ejoinAct {d : ℕ} {G : Type*} [AddGroup G] (g : G) (μ : Fin (d + 1) × G → ℝ) :
    Fin (d + 1) × G → ℝ :=
  fun v => μ (v.1, -g + v.2)

end TreeCoverLB


