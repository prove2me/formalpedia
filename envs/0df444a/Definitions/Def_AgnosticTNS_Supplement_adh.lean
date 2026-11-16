-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_adh
-- name    : AgnosticTNS_Supplement_adh
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:36:10.304447+00:00
-- url     : https://prove2.me/theorems/f5ed8bba-a4f5-4a6a-8637-b7d118650091
-- title:
--   Adhesion $\mathrm{adh}(t)$ in a tree-cut decomposition
-- statement:
--   Let $(\mathcal T,\mathcal X)$ be a tree-cut decomposition of $G$ with root $r$. For $t\neq r$ with parent $u$, deleting $\{u,t\}$ separates $\mathcal T$ into components $\mathcal T_u\ni u$ and $\mathcal T_t\ni t$, and
--   $$
--   \mathrm{adh}(t) = \Big|\mathrm{cut}_G\Big(\bigcup_{b\in V(\mathcal T_t)} X_b\Big)\Big|,
--   $$
--   the number of edges of $G$ joining bags on opposite sides; $\mathrm{adh}(r)=0$.
--
--   **Formalization Note** $\mathcal T_t$ is the set of nodes $s$ whose path to the root passes through $t$, i.e. $\mathrm{dist}(r,s)=\mathrm{dist}(r,t)+\mathrm{dist}(t,s)$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Definition 6.4, Eq. (6.2), p.48

import Mathlib
import Definitions.Def_AgnosticTNS_Supplement_TreeCutDecomp
import Definitions.Def_AgnosticTNS_cut

namespace AgnosticTNS.Supplement

/-- **The adhesion** `adh(t)`, Eq. (6.2), Definition 6.4, p.48 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
for `t ≠ r`, `|cut_G(⋃_{b ∈ V(𝒯_t)} X_b)|`, where `𝒯_t` is the component containing `t` after deleting
the edge from `t` to its parent; `adh(r) = 0`.

**Formalization Note** `𝒯_t` is the set of nodes `s` whose path to the root passes through `t`, i.e.
`dist(r, s) = dist(r, t) + dist(t, s)`. -/
noncomputable def adh {n : ℕ} (G : SimpleGraph (Fin n)) (D : TreeCutDecomp n) (t : Fin D.N) : ℕ := by
  classical
  exact if t = D.root then 0 else
    (cut G ((Finset.univ.filter fun s => D.T.dist D.root s = D.T.dist D.root t + D.T.dist t s).biUnion
      D.X)).card

end AgnosticTNS.Supplement


