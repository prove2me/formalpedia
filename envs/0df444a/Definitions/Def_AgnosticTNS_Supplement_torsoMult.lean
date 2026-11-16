-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_torsoMult
-- name    : AgnosticTNS_Supplement_torsoMult
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:36:36.60019+00:00
-- url     : https://prove2.me/theorems/d6c1b5c9-ac22-418b-b866-52ea5437ea92
-- title:
--   Torso $H_t$ of a tree-cut decomposition (edge multiplicities)
-- statement:
--   Fix a node $t$ of a tree-cut decomposition $(\mathcal T,\mathcal X)$ of $G$ and let $\mathcal T_1,\dots,\mathcal T_\ell$ be the components of $\mathcal T-t$. The **torso** $H_t$ is the multigraph obtained from $G$ by contracting each set $Z_i=\bigcup_{s\in V(\mathcal T_i)}X_s$ to a single vertex $z_i$, preserving parallel edges and deleting loops (an empty $Z_i$ gives an isolated $z_i$). The vertices of $X_t$ are the core vertices, the $z_i$ the peripheral vertices. Its edge multiplicities are: $1$ or $0$ between core vertices (adjacency in $G$); the number of $G$-neighbours of $v$ in $Z_i$ between a core vertex $v$ and $z_i$; the number of $G$-edges between $Z_i$ and $Z_j$ between $z_i$ and $z_j$; and $0$ on the diagonal.
--
--   **Formalization Note** The peripheral vertex of the component containing the neighbour $u$ of $t$ is labelled by $u$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Definition 6.5, Eq. (6.3), p.48

import Mathlib
import Definitions.Def_AgnosticTNS_Supplement_TreeCutDecomp
import Definitions.Def_AgnosticTNS_Supplement_treeSide

namespace AgnosticTNS.Supplement

/-- **The torso `H_t` as an edge-multiplicity matrix**, Definition 6.5, p.48 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)).
The vertices of `H_t` are the core vertices `X_t` (`Sum.inl v`) and one peripheral vertex `z_u` per
component `𝒯_u` of `𝒯 − t` (`Sum.inr u`, `u` the neighbour of `t` in that component); `z_u` is obtained by
contracting `Z_u = ⋃_{s ∈ V(𝒯_u)} X_s`, preserving parallel edges and deleting loops. The multiplicity
of the pair `{a, b}` is: `1` or `0` between core vertices (adjacency in `G`), the number of
`G`-neighbours of `v` in `Z_u` between `v` and `z_u`, and the number of `G`-edges between `Z_u` and
`Z_{u'}` between `z_u` and `z_{u'}`; the diagonal is `0` (loops deleted). An empty `Z_u` gives an
isolated `z_u`.

**Formalization Note** The vertex set of `H_t` is `X_t ⊕ {u : u ~ t in 𝒯}` (see `tor`); the matrix is
symmetric. -/
noncomputable def torsoMult {n : ℕ} (G : SimpleGraph (Fin n)) (D : TreeCutDecomp n) (t : Fin D.N) :
    Fin n ⊕ Fin D.N → Fin n ⊕ Fin D.N → ℕ := by
  classical
  exact fun a b => match a, b with
    | Sum.inl u, Sum.inl v => if u ≠ v ∧ G.Adj u v then 1 else 0
    | Sum.inl u, Sum.inr s => ((treeSide D.T t s).biUnion D.X |>.filter fun v => G.Adj u v).card
    | Sum.inr s, Sum.inl u => ((treeSide D.T t s).biUnion D.X |>.filter fun v => G.Adj u v).card
    | Sum.inr s, Sum.inr s' => if s = s' then 0 else
        (((treeSide D.T t s).biUnion D.X ×ˢ (treeSide D.T t s').biUnion D.X).filter
          fun p => G.Adj p.1 p.2).card

end AgnosticTNS.Supplement


