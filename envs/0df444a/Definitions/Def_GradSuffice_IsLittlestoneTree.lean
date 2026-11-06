-- Prove2me | Definitions.Def_GradSuffice_IsLittlestoneTree
-- name    : GradSuffice_IsLittlestoneTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:38.238395+00:00
-- url     : https://prove2.me/theorems/3e2b22a6-f0cd-4923-8b61-4eec2a7b38ae
-- title:
--   Littlestone tree for a partial concept class
-- statement:
--   Let $H$ be a class of **partial concepts** $h:Z\to\{0,1,\star\}$, where $\star$ means undefined. A **Littlestone tree** of depth $d$ for $H$ is a complete binary tree of depth $d$ whose internal vertices are labelled by elements of $Z$ and whose two outgoing edges at each vertex are labelled $0$ and $1$, such that every root-to-leaf path is realized by some $h\in H$: $h(z)=y$ whenever the path takes the edge labelled $y$ out of a vertex labelled $z$.
--
--   **Formalization Note** A partial concept is `Z → Option Bool` (`none` is $\star$; `false`, `true` are $0$, $1$). A path is a string $b\in\{0,1\}^d$ and the vertex at depth $i$ on it is labelled $z_i(b_{<i})$.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), App. B.1, p.37

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_NondualOpt_histPrefix

namespace GradSuffice

/-- **Littlestone tree for a partial concept class.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, App. B.1, p.37: "Let `H` be a
nonempty class of partial concepts `h : Z → {0, 1, ⋆}` […]. A Littlestone tree for `H` is a
complete binary tree whose internal vertices are labeled by elements of `Z` and whose two outgoing
edges at each internal vertex are labeled `0` and `1`. For every root-to-leaf path, there must exist
`h ∈ H` such that `h(z) = y` whenever the path takes an edge labeled `y` from a vertex labeled `z`."

**Formalization Note.** A partial concept is `Z → Option Bool` (`none` is `⋆`, `false`/`true` are
`0`/`1`); a tree of depth `d` labelled by `Z` is a `NondualOpt.Tree Z d`, a root-to-leaf path is
`b : Fin d → Bool`, and the vertex at depth `i` on it is labelled `z i (b<ᵢ)`. -/
def IsLittlestoneTree {Z : Type*} (H : Set (Z → Option Bool)) {d : ℕ}
    (z : NondualOpt.Tree Z d) : Prop :=
  ∀ b : Fin d → Bool, ∃ h ∈ H, ∀ i : Fin d, h (z i (NondualOpt.histPrefix b i)) = some (b i)

end GradSuffice


